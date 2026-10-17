---
article_id: af_995dc8bb6d1e449e415922d5
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsCFiniteSequence
---

# CFinite Sequence

A polynomial sequence is C-finite (concept `jis_sem_35aa465b4e5a8b902eabc445`,
source statement `jis_1ebc476d74ad111e89710ced`):
there exist `k`, `N`, and polynomials `p₁, …, pₖ` in `ZZ[bar{x}]`,
here `MvPolynomial σ ℤ`, such that for all `n ≥ N` the `(n + k + 1)`-st term
equals `∑_{i=1}^k pᵢ` times the `(n + i)`-th term, i.e.
`a (n + k + 1) = ∑ i : Fin k, c i * a (n + i.val + 1)`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.CFiniteSequence](../../../../../../sources/v2/MathlibExt.md)
