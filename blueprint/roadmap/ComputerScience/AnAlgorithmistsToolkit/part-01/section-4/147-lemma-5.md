---
article_id: af_a058e2cf893e449002d6d84c
declaration: theorem
origin: cited
statement: formalized
lean: LLL.reduced_basis_bounds_lemma5
---

# Lemma 5 (Section 4.2.2)

For a reduced basis $b_1, \ldots, b_n$ ordered as above, $\prod_{i=1}^{n} \|b_i\| \leq 2^{n(n-1)/4} \det(L)$. Consequently, if we let $H = \operatorname{span}(b_1, \ldots, b_{n-1})$, then $2^{-n(n-1)/4} \|b_n\| \leq \operatorname{dist}(H, b_n) \leq \|b_n\|$.

## Depends on

- [Definition 6 (Reduced bases)](../../part-02/lecture-19/128-reduced-bases.md)
- [Definition (Determinant of lattice)](../../part-02/lecture-18/137-determinant-of-lattice.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Section 4.2.2](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
