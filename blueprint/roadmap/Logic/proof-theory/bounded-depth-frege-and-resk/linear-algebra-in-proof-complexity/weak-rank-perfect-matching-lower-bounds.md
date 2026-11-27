# Perfect matching encoding of the weak rank principle is hard

For every $m>n$, the perfect matching CNF encoding of the weak rank principle needs size $2^{\Omega(n)}$ in $\mathrm{PCR}_{\mathbb F_2}$ (for $A=I_m$), in $\mathrm{PCR}_{\mathbb F}$ with $\mathrm{char}\,\mathbb F\ne2$ and in Sum-of-Squares (for every rational $A$), and size $2^{n^{\Omega(1)}}$ in bounded-depth Frege.

**Theorem.** For every $m>n$, every $\mathrm{PCR}_{\mathbb F_2}$ refutation of the perfect matching CNF encoding $\mathrm{PMRank}^m_n(I_m)$ requires size $2^{\Omega(n)}$.

**Theorem.** For every $m>n$ and $A\in\mathbb Q^{m\times m}$, any $\mathrm{PCR}_{\mathbb F}$ refutation, for a field $\mathbb F$ with $\mathrm{char}(\mathbb F)\ne2$, or Sum-of-Squares refutation of $\mathrm{PMRank}^m_n(A)$ requires size $2^{\Omega(n)}$. Similarly, any [bounded-depth Frege](../bounded-depth-frege-systems/bounded-depth-frege-proofs.md) refutation requires size $2^{n^{\Omega(1)}}$, where the constant in the exponent depends on the depth.

Here $\mathrm{PMRank}^m_n(A)$ is the perfect matching encoding of the [weak rank principle](weak-rank-principle.md), and refutations exist only when it is unsatisfiable.

## Expansion

Over $\mathbb F_2$ the perfect matching principle (no perfect matching on an odd set) is itself easy for $\mathrm{PCR}_{\mathbb F_2}$, so the first bound does not come from the encoding; it needs a notion of degree different from the algebraic encoding's, which is reused for the Sherali-Adams bounds. This contrasts with many known cases where hardness comes from the perfect matching principle itself, as the source shows for $\mathrm{PCR}_{\mathbb F}$ with $\mathrm{char}(\mathbb F)\ne2$. Encoding equations by matchings on their satisfied monomials is the same device as the [reductions behind counting axioms](../modular-counting-principles/reductions-to-polynomial-systems.md). Although the perfect matching encoding gives generators against several systems, it is not known how to derive hardness of circuit lower bound statements from it, unlike the [bamboo-tree encoding](weak-rank-pcr-f2-lower-bounds.md).

## Depends on

- [The weak rank principle](weak-rank-principle.md)
- [Bounded-depth Frege proofs](../bounded-depth-frege-systems/bounded-depth-frege-proofs.md)

## Proof depends on

None.

## Sources

- Michal Garlík, Svyatoslav Gryaznov, Hanlin Ren and Iddo Tzameret, "The Weak Rank Principle: Lower Bounds and Applications", *58th Annual ACM Symposium on Theory of Computing (STOC 2026)*, 2026, https://doi.org/10.1145/3798129.3800735; numbering as in arXiv:2608.08760v1 (Section 2.1, Theorems 2.2 and 2.3).
