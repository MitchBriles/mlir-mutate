#!/usr/bin/env python3

from __future__ import annotations

import argparse
from collections import defaultdict
from pathlib import Path


def parse_pattern_file(path: Path) -> tuple[int, str]:
    text = path.read_text(encoding="utf-8")
    first_line, sep, rest = text.partition("\n")
    if not sep:
        raise ValueError(f"missing IR body after count in {path}")
    count = int(first_line.strip())
    return count, rest


def aggregate_patterns(root: Path) -> list[tuple[str, int]]:
    totals: dict[str, int] = defaultdict(int)
    for pattern_file in sorted(root.glob("*/*.ll")):
        if pattern_file.parent.name == "total":
            continue
        count, ir = parse_pattern_file(pattern_file)
        totals[ir] += count
    return sorted(totals.items(), key=lambda item: (-item[1], item[0]))


def write_aggregated_patterns(total_dir: Path, aggregated: list[tuple[str, int]]) -> None:
    total_dir.mkdir(parents=True, exist_ok=True)
    for old_file in total_dir.glob("pattern_*.ll"):
        old_file.unlink()
    for idx, (ir, count) in enumerate(aggregated):
        out_path = total_dir / f"pattern_{idx}.ll"
        out_path.write_text(f"{count}\n{ir}", encoding="utf-8")


def first_non_empty_line(text: str) -> str:
    for line in text.splitlines():
        if line.strip():
            return line.strip()
    return "<empty pattern>"


def main() -> None:
    parser = argparse.ArgumentParser(description="Aggregate canonicalized LLVM pattern counts.")
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("temp/PROJ_out"),
        help="Root directory containing per-project pattern subdirectories.",
    )
    parser.add_argument(
        "--top",
        type=int,
        default=10,
        help="How many top patterns to print.",
    )
    args = parser.parse_args()

    root = args.root
    total_dir = root / "total"
    aggregated = aggregate_patterns(root)
    write_aggregated_patterns(total_dir, aggregated)

    print(f"Aggregated {len(aggregated)} unique patterns into {total_dir}")
    print(f"Top {min(args.top, len(aggregated))} patterns:")
    for idx, (ir, count) in enumerate(aggregated[: args.top], start=1):
        preview = first_non_empty_line(ir)
        print(f"{idx}. {count} :: {preview}")


if __name__ == "__main__":
    main()
