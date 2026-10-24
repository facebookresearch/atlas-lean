---
article_id: af_e679ff013e8caaabd3a9eb6b
declaration: def
origin: cited
statement: formalized
lean: PermutationStability.flexibleHammingDistance
---

# Flexible Hamming Distance

Flexible Hamming distance between a small permutation `σ` of `Fin n` and a
large permutation `τ` of `Fin m` (with `h : n ≤ m`): the disagreement count on
the embedded copy plus the `m - n` unmatched points, normalized by `n`.

Kourovka 21.84 is internally inconsistent about the argument order: it first
defines the distance with the small permutation first, `d_n^flex(σ, τ)` for
`σ ∈ S_n`, `τ ∈ S_m`, but later writes the convergence expression with
`ρ_n(g)` first. This formalization follows the definition site (small first),
which is also the type-correct order for the embedding `Fin n → Fin m`.

As above, the `n = 0` denominator is harmless for `Filter.atTop`
convergence.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.GroupTheory.PermutationStability](../../../../../sources/v2/MathlibExt.md)
