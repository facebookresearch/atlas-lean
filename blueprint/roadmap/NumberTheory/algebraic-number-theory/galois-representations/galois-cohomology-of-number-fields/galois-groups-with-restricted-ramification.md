# Galois groups with restricted ramification and their modules

Let $F$ be a number field and $S$ a set of places of $F$ containing the set $S_\infty$ of archimedean
places. Fix an algebraic closure $\bar F$. Let $F_S \subseteq \bar F$ be the maximal extension of $F$
unramified outside $S$ and $G_S = \operatorname{Gal}(F_S/F)$, a quotient of $G_F = \operatorname{Gal}(\bar F/F)$.
Let $\mathbb{N}(S)$ be the set of positive integers $n$ that are units in the ring
$\mathcal{O}_{F,S}$ of $S$-integers, that is, whose prime divisors $p$ satisfy $S_p \subseteq S$, where $S_p$
is the set of places above $p$.

- $\operatorname{Mod}_S(G_S)$ is the category of discrete $G_S$-modules $A$ that are finitely generated as
  abelian groups and whose torsion subgroup has order in $\mathbb{N}(S)$. The **dual** of $A$ is
  $A' = \operatorname{Hom}(A, \mathcal{O}_S^\times)$, where $\mathcal{O}_S^\times$ is the group of $S$-units of $F_S$;
  for finite $A$ of order in $\mathbb{N}(S)$, $A' = \operatorname{Hom}(A, \mu)$, with $\mu$ the roots of unity
  of $F_S$, since $F_S$ contains the $n$-th roots of unity for every $n \in \mathbb{N}(S)$.
- For a place $v$ of $F$ let $F_v$ be the completion and fix an $F$-embedding $\bar F \to \bar F_v$; it
  identifies $G_v = \operatorname{Gal}(\bar F_v/F_v)$ with a decomposition group in $G_F$, and composing with
  $G_F \to G_S$ gives restriction maps $H^i(G_S, A) \to H^i(F_v, A) = H^i(G_v, A)$, independent of the
  choice of embedding up to the conjugation action, which is trivial on cohomology. For archimedean $v$,
  $H^0(F_v, A)$ is replaced by the Tate cohomology group $\hat H^0(F_v, A)$ in what follows.
- For $i \ge 0$, $P^i(G_S, A)$ is the restricted product of the groups $H^i(F_v, A)$, $v \in S$, with
  respect to the unramified classes $H^i_{\mathrm{nr}}(F_v, A)$; for finite $S$ it is the product. The
  **localization map** $\lambda^i \colon H^i(G_S, A) \to P^i(G_S, A)$ is defined, since every class is
  unramified at almost all places of $S$; the same holds with $A'$ in place of $A$.

## Depends on

- [Cohomology of profinite groups](../../../../RepresentationTheory/group-cohomology/cohomology-of-profinite-groups.md), for the cohomology of $G_S$ and of the decomposition groups
- [Unramified classes under local duality](../galois-cohomology-of-local-fields/unramified-classes-under-local-duality.md), for the unramified classes $H^i_{\mathrm{nr}}$

## Proof depends on

- [Global duality for Galois groups with restricted ramification](global-duality-for-galois-groups-with-restricted-ramification.md), for $\mu_n \subseteq F_S$ when $n \in \mathbb{N}(S)$, and for the localization maps landing in the restricted products

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter VIII, §3, p. 452 (the
  set $S \supseteq S_\infty$, $k_S$, $G_S$, $\mathbb{N}(S)$), (8.3.4) Proposition ($\mu_n \subseteq k_S$ for
  $n \in \mathbb{N}(S)$); §5, (8.5.1) Definition ($\operatorname{Mod}_S(G_S)$); §6, p. 480 (the dual
  $A' = \operatorname{Hom}(A, \mathcal{O}_S^\times)$ and the convention on local duals), (8.6.1) Proposition and
  (8.6.2) Definition (the localization maps into $P^i(G_S, M)$, with $\hat H^0$ at the archimedean places).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, §4 (the groups $G_S$, $P^r_S(K, M)$ and the maps $\beta^r_S$ before Theorem 4.10).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  defines $G_S$ as `ReciprocityTheory.Gal.GS` and the restriction to decomposition groups as
  `ReciprocityTheory.Gal.locFam`.
