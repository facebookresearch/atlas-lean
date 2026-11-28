# Galois cohomology of roots of unity over a p-adic field

Let $k$ be a finite extension of $\mathbb{Q}_p$ with algebraic closure $\bar k$ and absolute Galois group
$G_k$, let $\mu \subset \bar k^\times$ be the group of roots of unity and $\mu_n$ its subgroup of $n$-th
roots of unity, $n \ge 1$, and write $H^i(k, A) = H^i(G_k, A)$ for a discrete $G_k$-module $A$. Then

$$H^0(k, \mu_n) = \mu_n(k), \qquad H^1(k, \mu_n) \cong k^\times / k^{\times n}, \qquad
H^2(k, \mu_n) \cong \tfrac{1}{n}\mathbb{Z}/\mathbb{Z},$$

where the second isomorphism sends the class of $a \in k^\times$ to the class of the cocycle
$\sigma \mapsto \sigma(\alpha)/\alpha$ for any $\alpha \in \bar k$ with $\alpha^n = a$ (the Kummer map),
and the third is induced by the invariant map $\operatorname{inv}_k \colon H^2(k, \bar k^\times) \to \mathbb{Q}/\mathbb{Z}$
of local class field theory. These identifications come from the Kummer sequence
$1 \to \mu_n \to \bar k^\times \xrightarrow{n} \bar k^\times \to 1$ together with
$H^1(k, \bar k^\times) = 1$ and $H^2(k, \bar k^\times) \cong \mathbb{Q}/\mathbb{Z}$. Passing to the direct limit
over $n$, they give a canonical isomorphism $H^2(k, \mu) \cong \mathbb{Q}/\mathbb{Z}$, under which
$H^2(k, \mu_n) \to H^2(k, \mu)$ is the inclusion of $\tfrac1n \mathbb{Z}/\mathbb{Z}$. In particular, for every
prime $\ell$ and $r \ge 1$, $H^2(k, \mu_{\ell^r}) \cong \mathbb{Z}/\ell^r\mathbb{Z}$.

## Depends on

- [Cohomology of a profinite group with discrete coefficients](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/cohomology-with-discrete-coefficients.md), for the cohomology of $G_k$ with discrete coefficients
- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for the invariant map $\operatorname{inv}_k$ (its item 2)

## Proof depends on

- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for $H^1(k, \bar k^\times) = 1$ and $\operatorname{inv}_k \colon H^2(k, \bar k^\times) \cong \mathbb{Q}/\mathbb{Z}$, by passage to the limit over finite Galois extensions (its item 2)
- [The long exact cohomology sequence](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/long-exact-cohomology-sequence.md), for the long exact cohomology sequence
- [Cohomology commutes with direct limits](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/cohomology-commutes-with-direct-limits.md), for the commutation of cohomology with direct limits

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren der
  mathematischen Wissenschaften 323, Springer, 2008; electronic edition, version 2.3 (May 2020),
  <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: (7.1.8) Theorem (ii) and its proof (the Kummer
  sequence with $H^1(k, \bar k^\times) = 1$ and $H^2(k, \bar k^\times) \cong \mathbb{Q}/\mathbb{Z}$), and (7.1.9)
  Corollary ($H^2(k, \mu) \cong \mathbb{Q}/\mathbb{Z}$ canonically for a $p$-adic field $k$), pp. 376–377.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., BookSurge, 2006,
  <https://www.jmilne.org/math/Books/ADTnot.pdf>: Chapter I, proof of Theorem 2.1 (the table of
  $H^r(G, \mu_n(K^s))$ for $r = 0, 1, 2, 3$).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  includes $H^2(G_k, \mu_{\ell^r}) \cong \mathbb{Z}/\ell^r\mathbb{Z}$ in
  `Formalism.GaloisCohomology.LocalTateDualityK`.
