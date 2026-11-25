# Galois cohomology of ℓ-adic representations of a p-adic field

Let $K$ be a finite extension of $\mathbb{Q}_p$, $\ell$ a prime (equal to $p$ or not), $V$ a
finite-dimensional $\mathbb{Q}_\ell$-vector space with a continuous linear action of $G_K$, and $T \subset V$
a $G_K$-stable $\mathbb{Z}_\ell$-lattice. Cohomology is the continuous cochain cohomology, with $V$ and $T$
carrying their $\ell$-adic topologies.

1. **Passage from finite coefficients.** $H^i(G_K, T)$ is a finitely generated $\mathbb{Z}_\ell$-module,
   $H^i(G_K, T) = \varprojlim_n H^i(G_K, T/\ell^n T)$, and $H^i(G_K, V) \cong H^i(G_K, T) \otimes_{\mathbb{Z}_\ell} \mathbb{Q}_\ell$.
2. **Cohomological dimension.** $H^i(G_K, V) = 0$ for $i > 2$.
3. **Duality.** For the Tate module $T_\ell(\mu) = \varprojlim_m \mu_{\ell^m}$ of $\mathbb{G}_m$, item 1 and the
   isomorphisms $H^2(G_K, \mu_{\ell^m}) \cong \mathbb{Z}/\ell^m\mathbb{Z}$ given by the invariant map, compatible with the
   transition maps, give a canonical isomorphism
   $H^2(G_K, T_\ell(\mu)) = \varprojlim_m H^2(G_K, \mu_{\ell^m}) \cong \varprojlim_m \mathbb{Z}/\ell^m\mathbb{Z} = \mathbb{Z}_\ell$, and
   tensoring with $\mathbb{Q}_\ell$ gives $H^2(G_K, V_\ell(\mu)) \cong \mathbb{Q}_\ell$ for the rational Tate module
   $V_\ell(\mu) = T_\ell(\mu) \otimes_{\mathbb{Z}_\ell} \mathbb{Q}_\ell$. For the scalar-character model $\mathbb{Q}_\ell(1)$ the
   isomorphism depends on a choice of compatible primitive $\ell^m$-th roots of unity.
   For $i = 0, 1, 2$ the cup product $H^i(G_K, V) \times H^{2-i}(G_K, V^*(1)) \to H^2(G_K, \mathbb{Q}_\ell(1)) \cong \mathbb{Q}_\ell$
   is a perfect pairing of finite-dimensional $\mathbb{Q}_\ell$-vector spaces.
4. **Euler characteristic.** $\dim H^0(G_K, V) - \dim H^1(G_K, V) + \dim H^2(G_K, V)$ is $0$ if $\ell \ne p$
   and $-[K : \mathbb{Q}_p] \dim V$ if $\ell = p$.

## Depends on

- [Cyclotomic character and Tate twists](../cyclotomic-character-and-tate-twists.md), for $V^*(1)$ and $\mathbb{Q}_\ell(1)$
- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for continuous cochain cohomology

## Proof depends on

- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for Tate's comparison of continuous cohomology with the inverse limit over finite levels when the cohomology of the open subgroups with $\mathbb{Z}/\ell$-coefficients is finite
- [Cohomological dimension and finiteness for p-adic fields](cohomological-dimension-of-p-adic-fields.md), for the finiteness of $H^i(U, \mathbb{Z}/\ell\mathbb{Z})$ for open subgroups $U$ and for $\operatorname{cd}_\ell(G_K) = 2$
- [Local Tate duality](local-tate-duality.md), applied to $T/\ell^n T$
- [Galois cohomology of roots of unity over a p-adic field](cohomology-of-roots-of-unity-over-p-adic-fields.md), for the isomorphisms $H^2(G_K, \mu_{\ell^m}) \cong \mathbb{Z}/\ell^m\mathbb{Z}$, whose inverse limit is $H^2(G_K, T_\ell(\mu)) \cong \mathbb{Z}_\ell$
- [Local Euler characteristic formula](local-euler-characteristic-formula.md), applied to $T/\ell^n T$

## Sources

- J. Bellaïche, *An introduction to the conjecture of Bloch and Kato*, Clay Mathematics Institute summer
  school, 2009, <http://virtualmath1.stanford.edu/~conrad/BSDseminar/refs/BKintro.pdf>: §2.1.1, condition
  Fin($p$), Exercise 2.1 c (local fields satisfy it) and Proposition 2.1 (Tate; item 1), with Lemmas 2.1–2.4;
  §2.1.3, Proposition 2.2 (items 2–4 for a finite extension $K$ of $\mathbb{Q}_l$ and a $p$-adic
  representation, in Bellaïche's letters). Bellaïche prints the right-hand side of the Euler characteristic
  formula for $l = p$ as $[K : \mathbb{Q}_p] \dim V$; the sign is negative, as his formula for
  $\dim H^1(G_K, V)$ right after it shows and as in Neukirch–Schmidt–Wingberg (7.3.8).
- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter II, §7, (2.7.5),
  (2.7.6), (2.7.10)–(2.7.12) (continuous cochain cohomology of $\mathbb{Z}_\ell$-modules); (7.3.8) Corollary (the
  Euler characteristic of $\mathbb{Z}_\ell(j)$, equal to $-[k : \mathbb{Q}_p]$ for $\ell = p$).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the duality for $p$-adic representations inside `GlobalTheory.Published.BlochKatoLocal`.
