# Global Euler characteristic formula

Let $F$ be a number field, $S$ a finite set of places of $F$ containing the archimedean places, $G_S$ the
Galois group of the maximal extension of $F$ unramified outside $S$, and $A$ a finite $G_S$-module whose
order is in $\mathbb{N}(S)$. Then

$$\chi_2(G_S, A) = \frac{\# H^0(G_S, A) \cdot \# H^2(G_S, A)}{\# H^1(G_S, A)}
= \prod_{v \in S_\infty} \frac{\# H^0(F_v, A)}{\lVert \# A \rVert_v},$$

where $H^0(F_v, A) = A^{G_v}$ is the group of invariants (ordinary cohomology, not the Tate group
$\hat H^0$ used in the restricted product $P^0$), and $\lVert \# A \rVert_v = \# A$ for $v$ real and
$(\# A)^2$ for $v$ complex. Equivalently,
$\# H^0(G_S, A) \cdot \# H^2(G_S, A) \cdot (\# A)^{[F : \mathbb{Q}]} = \# H^1(G_S, A) \cdot \prod_{v \in S_\infty} \# H^0(F_v, A)$,
and when $F$ is totally imaginary, $\chi_2(G_S, A) = (\# A)^{-[F : \mathbb{Q}]/2}$.

## Depends on

- [Galois groups with restricted ramification and their modules](galois-groups-with-restricted-ramification.md)
- [Finiteness and cohomological dimension of Galois groups with restricted ramification](finiteness-and-cohomological-dimension-of-g-s.md), for the finiteness of the groups

## Proof depends on

- [Poitou–Tate exact sequence](poitou-tate-exact-sequence.md), whose exactness gives $\varphi(G_S, A) \varphi(G_S, A') = 1$ by (8.6.13)(i)
- [Exactness of the Poitou–Tate complex](exactness-of-the-poitou-tate-complex.md), for the sequence (8.6.12), the quotient $\varphi(G_S, A)$ and its multiplicativity (8.6.13)
- [Global duality for Galois groups with restricted ramification](global-duality-for-galois-groups-with-restricted-ramification.md), for the cohomology of the $S$-units and their Galois module structure (NSW (8.3.11), (8.7.1)–(8.7.3))
- [Local Euler characteristic formula](../galois-cohomology-of-local-fields/local-euler-characteristic-formula.md)
- [Induction from cyclic subgroups in Grothendieck groups of modular representations](../../../../GroupTheory/characters-of-finite-groups/induction-from-cyclic-subgroups.md), which reduces the formula to cyclic extensions of degree prime to $p$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: the definition of $\chi_2$
  before (8.7.4); (8.7.4) Global Euler–Poincaré Characteristic Formula with Remarks 1–3 and its proof
  (through (8.6.12), (8.6.13), (8.7.3) and (7.3.4)), pp. 506–509.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Theorem 5.1 with footnote 13 ("$H^0(G_v, M) = M^{G_v}$ (it is not the Tate cohomology)") and
  Remark 5.2.
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the second form, with $\prod_{v \in S_\infty} \# H^0(F_v, A)$ written through complex conjugations, as
  `ReciprocityTheory.Gal.GlobalEulerChar`.
