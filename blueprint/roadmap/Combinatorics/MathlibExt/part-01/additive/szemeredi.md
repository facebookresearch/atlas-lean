---
article_id: af_883d6b4195abbeb80c01fd38
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Combinatorics.Additive.SzemerediWanted.szemeredi
---

# Szemeredi

For every `k ≥ 1` and `δ > 0` there is `N` such that every `n ≥ N` and every `A ⊆ Finset.range n`
with `δ * (n : ℝ) ≤ (A.card : ℝ)` contains `a, d` with `0 < d` and `a + i * d ∈ A` for all `i <
k`. Source: E. Szemerédi, Acta Arith. 27 (1975); Lean states finitary density form equivalent to
infinitary positive upper density k-AP existence.

Proof: We derive the result from the density Hales–Jewett theorem by averaging coordinate-sum
translates and mapping combinatorial lines to arithmetic progressions.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Density hales jewett](../../part-02/density-hales-jewett/density-hales-jewett.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Additive.Szemeredi](../../../../../sources/v2/MathlibExt.md)
