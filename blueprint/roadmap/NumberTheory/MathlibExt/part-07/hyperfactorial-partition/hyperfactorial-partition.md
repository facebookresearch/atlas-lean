---
declaration: structure
origin: cited
statement: formalized
lean: MetaMathlibExt.HyperfactorialPartition
---

# Hyperfactorial Partition

Hyperfactorial partition of `n` (concept `jis_sem_c632991dc77d0efec89f490f`,
source statement `jis_2803b664db749f0c99721a41`): a finite one-based digit list
`[h₁, …, hₖ]!` (clause `digits`) with `hᵢ ≤ 2 * i` for `1 ≤ i ≤ k`
(clause `bounds`, with `0 ≤ hᵢ` automatic for `ℕ`) and
`n = ∑_{i=1}^k hᵢ * i!` (clause `value`). Zero-based `Fin k` index `i`
translates to one-based source index `i.val + 1`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.HyperfactorialPartition](../../../../../sources/v2/MathlibExt.md)
