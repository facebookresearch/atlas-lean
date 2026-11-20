# Functional correctness

This section defines the observable order and occurrence-level stability
contract, proves correctness of each data-moving phase, and carries a
pending-run correctness invariant through the scan and final collapse.

## Specifications

- [Boolean strict-weak-order specification](order-and-stability.md)
- [Sorted-array specification](sorted-spec.md)
- [Occurrence-tagged stability specification](stable-spec.md)
- [Slice reversal preserves occurrence information](reverse-slice-correct.md)
- [Pending-run correctness invariant](pending-run-correctness.md)
- [Unscanned suffix matches the input snapshot](scan-remainder-matches.md)
- [Whole-entry snapshot permutation](entry-snapshot-permutation.md)

## Local correctness

- [`count_run` produces a stable sorted run](count-run-correct.md)
- [`binarysort` preserves and extends stable sortedness](binarysort-correct.md)
- [`gallop_left` partition specification](gallop-correct.md)
- [`gallop_right` partition specification](gallop-right-correct.md)
- [`merge_lo` stable correctness](merge-lo-correct.md)
- [`merge_hi` stable correctness](merge-hi-correct.md)
- [`merge_at` stable correctness](merge-correct.md)

## Assembly

- [Top-level scan preserves pending-run correctness](scan-step-correct.md)
- [Final collapse produces one correct run](force-collapse-correct.md)
- [Complete scan and final-collapse correctness](scan-loop-correct.md)
- [Execution equivariance](equivariance/README.md)
- [Reverse-mode order and stability algebra](reverse-mode-algebra.md)
- [Reverse-oriented scan transport](reverse-scan-transport.md)
- [Reverse mode implements the swapped order](reverse-mode-correct.md)
- [`listsort_correct`](listsort-correct.md)
