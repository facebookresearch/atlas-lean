# Dualizing module of a p-adic field

Let $k$ be a finite extension of $\mathbb{Q}_p$ with algebraic closure $\bar k$ and absolute Galois group
$G_k$, and let $\mu \subset \bar k^\times$ be the group of roots of unity. The dualizing module of the category of
discrete torsion $G_k$-modules is

$$D_0 = \varinjlim_{K, n} H^2(K, \mathbb{Z}/n\mathbb{Z})^*,$$

the limit over the finite extensions $K/k$ inside $\bar k$ and the integers $n \ge 1$, with
$X^* = \operatorname{Hom}(X, \mathbb{Q}/\mathbb{Z})$. It is characterized by functorial isomorphisms
$H^2(K, A)^* \cong \operatorname{Hom}_{G_K}(A, D_0)$ for every finite extension $K/k$ and every discrete torsion
$G_k$-module $A$. Then $D_0$ is canonically isomorphic to $\mu$ as a $G_k$-module: for every $K$ and $n$ the group
$\operatorname{Hom}_{G_K}(\mu_n, D_0) \cong H^2(K, \mu_n)^*$ is identified with $\mathbb{Z}/n\mathbb{Z}$ through the invariant
map, and the element corresponding to $1$ is an isomorphism of $\mu_n$ onto the $n$-torsion of $D_0$; these
isomorphisms fit together into $\mu \cong D_0$.

Under this identification, the cup-product pairings
$H^i(k, \operatorname{Hom}(A, \mu)) \times H^{2-i}(k, A) \to H^2(k, \mu)$ followed by the canonical isomorphism
$H^2(k, \mu) \cong \mathbb{Q}/\mathbb{Z}$ give the duality isomorphisms of the abstract duality theorem for $G_k$:
that theorem holds with its trace map $H^2(k, D_0) \to \mathbb{Q}/\mathbb{Z}$ replaced by any isomorphism.

## Depends on

- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for dualizing modules, their trace maps and cup products
- [Galois cohomology of roots of unity over a p-adic field](cohomology-of-roots-of-unity-over-p-adic-fields.md), for $H^2(K, \mu_n) \cong \mathbb{Z}/n\mathbb{Z}$ and $H^2(k, \mu) \cong \mathbb{Q}/\mathbb{Z}$

## Proof depends on

- [Galois cohomology of roots of unity over a p-adic field](cohomology-of-roots-of-unity-over-p-adic-fields.md), for $H^2(V, \mu_n) \cong \mathbb{Z}/n\mathbb{Z}$ for every open subgroup $V$ of $G_k$
- [Cohomological dimension and finiteness for p-adic fields](cohomological-dimension-of-p-adic-fields.md), for $\operatorname{scd}(G_k) = 2$, which makes $D_0$ a dualizing module
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for the theorem that a profinite group of finite strict cohomological dimension has a dualizing module, and for Remark 1 after the duality theorem (any isomorphism may replace the trace map)

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: the definition of $D_0$ before
  (7.2.4) ("$D_0 = \varinjlim_{K, n} H^2(K, \mathbb{Z}/n\mathbb{Z})^*$ … characterized by a functorial isomorphism
  $H^2(K, A)^* \cong \operatorname{Hom}_{G_K}(A, D_0)$"), p. 379; (7.2.4) Theorem ("The $G_k$-module $D_0$ is canonically
  isomorphic to the $G_k$-module $\mu$ of all roots of unity in $\bar k$") and its proof, p. 380; Chapter III, §4,
  (3.4.1) Theorem (dualizing module), the trace map, (3.4.3) Duality Theorem with Remark 1, and (3.4.6),
  pp. 182–185.
