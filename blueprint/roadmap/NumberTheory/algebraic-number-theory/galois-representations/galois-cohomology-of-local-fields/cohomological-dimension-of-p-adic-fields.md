# Cohomological dimension and finiteness for p-adic fields

Let $k$ be a finite extension of $\mathbb{Q}_p$ with absolute Galois group $G_k$. Then:

1. for every prime $\ell$ (including $\ell = p$), the cohomological $\ell$-dimension of $G_k$ is
   $\operatorname{cd}_\ell(G_k) = 2$; in particular $H^i(k, A) = 0$ for all $i \ge 3$ and every discrete torsion
   $G_k$-module $A$;
2. for every finite discrete $G_k$-module $A$, the groups $H^i(k, A)$ are finite for all $i \ge 0$;
3. for every discrete $G_k$-module $A$ that is finitely generated as an abelian group, $H^1(k, A)$ is
   finite.

Moreover, for every algebraic extension $L/k$ of degree divisible by $\ell^\infty$, in particular for the
maximal unramified extension, $\operatorname{cd}_\ell(G_L) \le 1$.

## Depends on

- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for cohomological dimension

## Proof depends on

- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for $H^1(K, \bar k^\times) = 0$ and the behaviour of the invariant map under restriction, $\operatorname{inv}_K \circ \operatorname{Res} = [K : k] \operatorname{inv}_k$, for the finite extensions $K/k$ (its item 2); for an infinite algebraic extension $L/k$ of degree divisible by $\ell^\infty$ these give $H^1(L, \bar k^\times) = 0$ and $H^2(L, \bar k^\times)(\ell) = \varinjlim_K H^2(K, \bar k^\times)(\ell) = 0$ by passage to the direct limit over the finite subextensions $K$ of $L/k$, along restriction maps that multiply the invariant by the degrees
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for the criterion for $\operatorname{cd}_\ell \le 1$ of a field in terms of $H^1$ and $H^2$ of the multiplicative group, the Hochschild–Serre spectral sequence and inflation–restriction
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for the commutation of cohomology with direct limits of groups used in that passage
- [Galois cohomology of roots of unity over a p-adic field](cohomology-of-roots-of-unity-over-p-adic-fields.md), for $H^2(k, \mu_\ell) \cong \mathbb{Z}/\ell\mathbb{Z} \ne 0$, which gives $\operatorname{cd}_\ell = 2$, and for $H^1(K, \mu_n) \cong K^\times/K^{\times n}$ and $H^2(K, \mu_n) \cong \tfrac1n\mathbb{Z}/\mathbb{Z}$ over finite extensions $K$
- [Index of the n-th powers in a local field of characteristic zero](../../../p-adic-numbers/index-of-n-th-powers.md), for the finiteness of $K^\times/K^{\times n}$, hence of $H^1(K, \mu_n)$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: (7.1.8) Theorem (i), (iii),
  (iv) with its proof (via (6.5.11) and the Hochschild–Serre spectral sequence for the maximal unramified
  extension), pp. 376–377, and the remark before it on p. 376 ($\mathrm{Br}(L)(p) = \varinjlim \mathrm{Br}(L_\alpha)(p) = 0$ over
  the finite subextensions $L_\alpha$ of an extension $L$ of degree divisible by $p^\infty$). NSW state the theorem
  for every local field, with $\operatorname{cd}_p = 1$ when $p$ is the characteristic.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Theorem 2.1 and the finiteness statements in its proof.
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the finiteness and the vanishing in degrees $\ge 3$ for finite $\mathbb{Z}/\ell^r\mathbb{Z}$-modules as
  `Formalism.GaloisCohomology.LocalFinitenessK` and `ReciprocityTheory.Gal.LocalFiniteness`.
