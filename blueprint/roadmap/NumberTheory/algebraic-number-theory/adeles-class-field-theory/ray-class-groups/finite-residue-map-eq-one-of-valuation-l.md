# Valuation criterion for the finite residue map to be trivial

Let $K$ be a number field,
$\mathfrak m$ a modulus of $K$ with finite part $\mathfrak m_0$, and $z$ a ray element of
$\mathfrak m$. Suppose that at every nonzero prime ideal $\mathfrak p$ of $\mathcal O_K$
containing $\mathfrak m_0$, the multiplicative $\mathfrak p$-adic valuation of $z - 1$ is at most
$\exp(-e_{\mathfrak p})$, where $e_{\mathfrak p}$ is the exponent of $\mathfrak p$ in
$\mathfrak m_0$; equivalently, $z = 1$ or $z - 1$ has $\mathfrak p$-adic order at least
$e_{\mathfrak p}$. Then the finite residue map of $\mathfrak m$ sends $z$ to $1$ in
$(\mathcal O_K / \mathfrak m_0)^\times$.

## Sources

- N406, Theorem 21.8, Section 21.3 (ATLAS NumberTheoryI item N406): the native-API finite-congruence step corresponding to [`finitePartMapHom_ker_iff`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1996-L2011), used by the weak-approximation argument before residue/sign surjectivity and by [`theorem_21_8_quotient_iso`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L2607-L2647). It is not the generalized weak-approximation theorem and not the final N406 result.
