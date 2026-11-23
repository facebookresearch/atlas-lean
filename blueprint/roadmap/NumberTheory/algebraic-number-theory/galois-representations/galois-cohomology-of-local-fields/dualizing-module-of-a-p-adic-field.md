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

This identification is what turns the abstract duality theorem for finite modules into local Tate duality,
for finite $G_k$-modules $A$ and degrees $0 \le i \le 2$; no duality statement for infinite torsion modules is made
here.

## Depends on

- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for dualizing modules
- [Galois cohomology of roots of unity over a p-adic field](cohomology-of-roots-of-unity-over-p-adic-fields.md), for the isomorphisms $H^2(K, \mu_n) \cong \mathbb{Z}/n\mathbb{Z}$ given by the invariant map

## Proof depends on

- [Cohomological dimension and finiteness for p-adic fields](cohomological-dimension-of-p-adic-fields.md), for $\operatorname{cd}_\ell(G_k) = 2$ for every prime $\ell$, so that the discrete torsion modules have a dualizing module $D_0$, which is also the dualizing module of every open subgroup
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for that dualizing module of a profinite group of finite cohomological dimension (NSW (3.4.4), and the remark after (3.4.1) on open subgroups)
- [Galois cohomology of roots of unity over a p-adic field](cohomology-of-roots-of-unity-over-p-adic-fields.md), for $H^2(V, \mu_n) \cong \mathbb{Z}/n\mathbb{Z}$ for every open subgroup $V$ of $G_k$, which identifies $\operatorname{Hom}_V(\mu_n, D_0)$ with $\mathbb{Z}/n\mathbb{Z}$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: the definition of $D_0$ before
  (7.2.4) ("$D_0 = \varinjlim_{K, n} H^2(K, \mathbb{Z}/n\mathbb{Z})^*$ … characterized by a functorial isomorphism
  $H^2(K, A)^* \cong \operatorname{Hom}_{G_K}(A, D_0)$"), p. 379; (7.2.4) Theorem ("The $G_k$-module $D_0$ is canonically
  isomorphic to the $G_k$-module $\mu$ of all roots of unity in $\bar k$") and its proof through (7.1.8), p. 380;
  Chapter III, §4, the remark after (3.4.1) (the dualizing module of an open subgroup) and (3.4.4) Theorem (the
  dualizing module $D_P$ when $\operatorname{cd}_P G = n < \infty$), pp. 182 and 185.
