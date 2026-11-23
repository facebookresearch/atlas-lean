# Integral Bloch–Kato conditions and their duality

This node is still to be broken down. It covers the Bloch–Kato local conditions with integral and torsion
coefficients and their duality, which pass from the $p$-adic statements of the
[Bloch–Kato orthogonality](bloch-kato-orthogonality.md) to lattices and divisible quotients. Let $K$ be a finite
extension of $\mathbb{Q}_p$, $V$ a de Rham $p$-adic representation of $G_K$, $T \subset V$ a $G_K$-stable lattice,
$V' = V^*(1)$ and $T' \subset V'$ the dual lattice. One defines $H^1_f(G_K, T)$ as the inverse image of
$H^1_f(G_K, V)$ under $H^1(G_K, T) \to H^1(G_K, V)$, and $H^1_f(G_K, V'/T')$ as the image of $H^1_f(G_K, V')$ in
$H^1(G_K, V'/T')$; the statement to be stated precisely is that they are the exact annihilators of each other
under the pairing $H^1(G_K, T) \times H^1(G_K, V'/T') \to H^2(G_K, \mathbb{Q}_p/\mathbb{Z}_p(1)) \cong \mathbb{Q}_p/\mathbb{Z}_p$.
It is kept as a node because no open source for it was checked: the sources named below are not freely
available, and their numbering of the definitions and of the duality statement has not been verified.

A good expansion has pages for the integral and torsion Bloch–Kato conditions, for the pairing between
$H^1(G_K, T)$ and $H^1(G_K, V'/T')$ obtained from local duality, and for the exact annihilator statement, each
with a checked locator in Bloch–Kato's §3 (around their Proposition 3.8) or in Flach's §1, which treats the
same conditions for the symmetric square of an elliptic curve.

## Depends on

- [Bloch–Kato subgroups of local Galois cohomology](bloch-kato-subgroups.md)
- [Galois cohomology of Tate twists over a p-adic field](../galois-cohomology-of-local-fields/cohomology-of-tate-twists-over-p-adic-fields.md), for $H^2(G_K, \mathbb{Q}_p/\mathbb{Z}_p(1)) \cong \mathbb{Q}_p/\mathbb{Z}_p$

## Proof depends on

- [Bloch–Kato orthogonality](bloch-kato-orthogonality.md)
- [Local Tate duality](../galois-cohomology-of-local-fields/local-tate-duality.md), for the duality at finite levels
- [Galois cohomology of ℓ-adic representations of a p-adic field](../galois-cohomology-of-local-fields/galois-cohomology-of-l-adic-representations.md), for the passage between $T$, $V$ and $V/T$

## Sources

- S. Bloch and K. Kato, "L-functions and Tamagawa numbers of motives", The Grothendieck Festschrift I,
  Progr. Math. 86, Birkhäuser, 1990, 333–400, §3 (not checked here).
- M. Flach, "A finiteness theorem for the symmetric square of an elliptic curve", Invent. Math. 109 (1992),
  307–327, §1 (not checked here).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the integral duality as the part `IntegralDuality` of `GlobalTheory.Published.BlochKatoLocal`.
