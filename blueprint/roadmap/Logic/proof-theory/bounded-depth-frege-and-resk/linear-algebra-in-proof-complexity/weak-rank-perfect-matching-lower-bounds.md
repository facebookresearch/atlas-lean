# Perfect matching encoding of the weak rank principle is hard

For every $m>n$, the perfect matching CNF encoding $\mathrm{PMRank}^m_n(A)$ of the weak rank principle needs size $2^{\Omega(n)}$ in $\mathrm{PCR}_{\mathbb F_2}$ for $A=I_m$, and, for every $A\in\{0,1\}^{m\times m}$, size $2^{\Omega(n)}$ in $\mathrm{PCR}_{\mathbb F}$ with $\mathrm{char}\,\mathbb F\ne2$ and in Sum-of-Squares, and size $2^{n^{\Omega(1)}}$ in bounded-depth Frege.

Here $\mathrm{PMRank}^m_n(A)$ is the perfect matching encoding of the [weak rank principle](weak-rank-principle.md) over the expressed field $\mathbb F_2$, defined for $A\in\{0,1\}^{m\times m}$, and [$\mathrm{PCR}_{\mathbb F}$](polynomial-calculus-resolution.md) refutes it through the polynomial translations of its clauses, with size the number of monomials. A *Sum-of-Squares* refutation of polynomials $f_1,\dots,f_k$ over $\mathbb R$ is a pair of sequences $(g_1,\dots,g_k)$ and $(h_1,\dots,h_\ell)$ of real polynomials with

$$
\sum_{i=1}^kf_ig_i+\sum_{j=1}^\ell h_j^2=-1,
$$

and its size is $\sum_i\|f_i\|\,\|g_i\|+\sum_j\|h_j\|$, where $\|f\|$ is the number of monomials of $f$ with nonzero coefficient. Refutations exist only when $\mathrm{PMRank}^m_n(A)$ is unsatisfiable.

**Theorem.** For every $m>n$, every $\mathrm{PCR}_{\mathbb F_2}$ refutation of $\mathrm{PMRank}^m_n(I_m)$ requires size $2^{\Omega(n)}$.

**Theorem.** For every $m>n$ and $A\in\{0,1\}^{m\times m}$, any $\mathrm{PCR}_{\mathbb F}$ refutation, for a field $\mathbb F$ with $\mathrm{char}(\mathbb F)\ne2$, or Sum-of-Squares refutation of $\mathrm{PMRank}^m_n(A)$ requires size $2^{\Omega(n)}$. Similarly, any [bounded-depth Frege](../bounded-depth-frege-systems/bounded-depth-frege-proofs.md) refutation requires size $2^{n^{\Omega(1)}}$, where the constant in the exponent depends on the depth.

## Expansion

Over $\mathbb F_2$ the perfect matching principle (no perfect matching on an odd set) is itself easy for $\mathrm{PCR}_{\mathbb F_2}$, so the first bound does not come from the encoding; it needs a notion of degree different from the algebraic encoding's, which is reused for the Sherali-Adams bounds. The second theorem, by contrast, reduces the perfect matching principles $\mathrm{Count}^2_n$ and $\mathrm{Count}^2_{n+1}$ to $\mathrm{PMRank}^m_n(A)$ whenever $A$ is neither all zeros nor all ones (otherwise the formula is satisfiable), and uses the known hardness of the perfect matching principle in those systems. Encoding equations by matchings on their satisfied monomials is the same device as the [reductions behind counting axioms](../modular-counting-principles/reductions-to-polynomial-systems.md). Although the perfect matching encoding gives generators against several systems, it is not known how to derive hardness of circuit lower bound statements from it, unlike the [bamboo-tree encoding](weak-rank-pcr-f2-lower-bounds.md).

## Depends on

- [The weak rank principle](weak-rank-principle.md)
- [Polynomial calculus resolution PCR_F](polynomial-calculus-resolution.md)
- [Bounded-depth Frege proofs](../bounded-depth-frege-systems/bounded-depth-frege-proofs.md)

## Proof depends on

None.

## Sources

- Michal Garlík, Svyatoslav Gryaznov, Hanlin Ren and Iddo Tzameret, "The Weak Rank Principle: Lower Bounds and Applications", *58th Annual ACM Symposium on Theory of Computing (STOC 2026)*, 2026, https://doi.org/10.1145/3798129.3800735; numbering as in arXiv:2608.08760v1 (Section 2.1, Theorems 2.2 and 2.3; Section 4.2, Definition 4.3 (Sum-of-Squares refutations and their size); Section 5.2, Definition 5.8 and Theorems 5.10 and 5.18).
