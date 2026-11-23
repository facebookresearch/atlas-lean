# Cohomological dimension and finiteness for p-adic fields

Let $k$ be a finite extension of $\mathbb{Q}_p$ with absolute Galois group $G_k$. Then:

1. for every prime $\ell$ (including $\ell = p$), the cohomological $\ell$-dimension and the strict
   cohomological $\ell$-dimension of $G_k$ are $\operatorname{cd}_\ell(G_k) = \operatorname{scd}_\ell(G_k) = 2$;
   in particular $H^i(k, A) = 0$ for all $i \ge 3$ and every discrete torsion $G_k$-module $A$;
2. for every finite discrete $G_k$-module $A$, the groups $H^i(k, A)$ are finite for all $i \ge 0$;
3. for every discrete $G_k$-module $A$ that is finitely generated as an abelian group, $H^1(k, A)$ is
   finite.

Moreover, for every algebraic extension $L/k$ of degree divisible by $\ell^\infty$, in particular for the
maximal unramified extension, $\operatorname{cd}_\ell(G_L) \le 1$.

## Depends on

- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for cohomological dimension and strict cohomological dimension

## Proof depends on

- [Local class field theory: cohomology and the existence theorem](../../../p-adic-numbers/local-class-field-theory-cohomology.md), for $H^1(L, \bar k^\times) = 0$ and the behaviour of the invariant map under restriction, $\operatorname{inv}_L \circ \operatorname{Res} = [L : k] \operatorname{inv}_k$, which give $H^2(L, \bar k^\times)(\ell) = 0$ when $\ell^\infty$ divides $[L : k]$ (its item 2)
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for the criterion for $\operatorname{cd}_\ell \le 1$ of a field in terms of $H^1$ and $H^2$ of the multiplicative group, the Hochschild–Serre spectral sequence, inflation–restriction and Serre's criterion for $\operatorname{scd}$
- [Galois cohomology of roots of unity over a p-adic field](cohomology-of-roots-of-unity-over-p-adic-fields.md), for $H^2(k, \mu_\ell) \cong \mathbb{Z}/\ell\mathbb{Z} \ne 0$, which gives $\operatorname{cd}_\ell = 2$, and for the finiteness of $H^i(K, \mu_n)$ over finite extensions $K$

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: (7.1.8) Theorem (i), (iii),
  (iv) with its proof (via (6.5.11) and the Hochschild–Serre spectral sequence for the maximal unramified
  extension), pp. 376–377; (7.2.5) Corollary ($\operatorname{scd}_p(k) = 2$ for every prime $p$, by Serre's
  criterion (3.4.5)), p. 380. NSW state the theorem for every local field, with $\operatorname{cd}_p = 1$ when
  $p$ is the characteristic.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Theorem 2.1 and the finiteness statements in its proof.
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the finiteness and the vanishing in degrees $\ge 3$ for finite $\mathbb{Z}/\ell^r\mathbb{Z}$-modules as
  `Formalism.GaloisCohomology.LocalFinitenessK` and `ReciprocityTheory.Gal.LocalFiniteness`.
