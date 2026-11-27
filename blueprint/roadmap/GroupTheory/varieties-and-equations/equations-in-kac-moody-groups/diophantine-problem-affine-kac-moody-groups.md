# The Diophantine problem in affine Kac–Moody groups over finite fields is undecidable

For an untwisted affine Kac–Moody group over a finite field with at least 4 elements whose underlying root system has rank at least 2, no algorithm decides whether a finite system of equations with coefficients in the group has a solution.

Let $A$ be an $n \times n$ indecomposable generalized Cartan matrix of untwisted affine type, and let $K$ be a field. The *affine Kac–Moody group* $\widetilde{G}_{sc}(A, K)$ is the value at $K$ of Tits's simply connected Kac–Moody group functor associated with $A$. The corresponding *loop group* is the adjoint elementary Chevalley group $E^{\Phi}_{ad}(K[t, t^{-1}])$ over the ring of Laurent polynomials, where $\Phi$ is the irreducible finite root system of which $A$ is the untwisted affinization; the quotient of the elementary subgroup $\widetilde{E}_{sc}(A, K)$ by its center is isomorphic to it. The rank in the theorem is the rank of the irreducible affine root system, as in the source. The *Diophantine problem* in a group $G$ asks, given a finite system of equations $w_i(x_1, \dots, x_m) = 1$ whose words involve the variables and finitely many constants from $G$, whether the system has a solution in $G$; for the finitely generated groups here, constants are given as words in a fixed finite generating set.

**Theorem (Morita and Plotkin).** Let $\mathbb{F}_q$ be a finite field with $q \geq 4$ and let $A$ be as above, of rank at least $2$. Then the Diophantine problem in the affine Kac–Moody group $\widetilde{G}_{sc}(A, \mathbb{F}_q)$ is undecidable (Proposition 15 of arXiv:2103.04575v3).

Proposition 15 of the source is stated for every finite field, but its proof interprets the coefficient ring through Corollary 13, which assumes $|\mathbb{F}_q| \geq 4$; the cases $q = 2, 3$ are not covered by the argument given.

For the loop groups $E^{\Phi}_{ad}(K[t, t^{-1}])$ with $\mathrm{rank}\, \Phi \geq 2$, the source shows that the Diophantine problem is Karp equivalent to the Diophantine problem in the ring $K[t, t^{-1}]$.

## Depends on

- [Group](../../group-basics/group.md)
- [Center of a group](../../group-basics/group-center.md)
- [Laurent polynomials](../../../AlgebraicGeometry/varieties-and-projective-geometry/tropical-varieties/laurent-poly.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Over a finite field the elementary subgroup of $\widetilde{G}_{sc}(A, \mathbb{F}_q)$ is finitely generated, so its center is defined by finitely many commutation equations, and the quotient by the center, the loop group $E^{\Phi}_{ad}(\mathbb{F}_q[t, t^{-1}])$, is interpretable by equations. In a Chevalley group of rank at least $2$, each root subgroup $X_\alpha$ is Diophantine and carries the ring structure of $\mathbb{F}_q[t, t^{-1}]$ through commutator relations, so the ring $\mathbb{F}_q[t, t^{-1}]$ is interpretable by equations in $\widetilde{G}_{sc}(A, \mathbb{F}_q)$. The source writes out this interpretation for $|\mathbb{F}_q| \geq 4$, using that the elementary subgroup is then perfect of finite commutator width (Corollary 13). A decision procedure for the group would then decide the Diophantine problem in $\mathbb{F}_q[t, t^{-1}]$, which is undecidable by a theorem of Pappas. A complete expansion links pages for the undecidability of the Diophantine problem of $\mathbb{F}_q[t, t^{-1}]$ (Pappas) and for the interpretation of the coefficient ring in Chevalley groups of rank at least $2$.

## Sources

- J. Morita and E. Plotkin, "Elementary equivalence and Diophantine problem of affine Kac–Moody groups", *International Journal of Algebra and Computation*, 2026, pp. 1–11 (online), doi:10.1142/S0218196726400126; read as arXiv:2103.04575v3, <https://arxiv.org/abs/2103.04575v3>: Section 2 (notation for affine Kac–Moody and loop groups), Corollaries 12 and 13 and Proposition 15 in the section on the Diophantine problem, with the numbering of that version.
- P. Pappas, "A Diophantine problem for Laurent polynomial rings", *Proceedings of the American Mathematical Society* 93(4):713–718, 1985, doi:10.1090/S0002-9939-1985-0776209-6 (cited beside the copy read for the undecidability of the Diophantine problem in $\mathbb{F}_q[t, t^{-1}]$).
