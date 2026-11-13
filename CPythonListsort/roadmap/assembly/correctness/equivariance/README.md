# Execution equivariance

These nodes prove that the transcribed evaluator is insensitive to proof-only
occurrence metadata in the two ways needed by top-level correctness. Origin
mirroring transports reverse-mode executions, while structural erasure links
the occurrence-enriched correctness run to the ordinary untagged evaluator.

## Reverse-mode relabeling

- [Origin-relabel equivariance support](origin-relabel-equivariance.md)
- [Merge evaluators commute with origin relabeling](merge-origin-equivariance.md)
- [Policy and complete scan commute with origin relabeling](scan-origin-equivariance.md)

## Occurrence erasure

- [Primitive evaluators ignore occurrence origins](occurrence-erasure-primitives.md)
- [Merge evaluators ignore occurrence origins](occurrence-erasure-merges.md)
- [The complete tagged sort erases to the untagged sort](occurrence-erasure-scan.md)
