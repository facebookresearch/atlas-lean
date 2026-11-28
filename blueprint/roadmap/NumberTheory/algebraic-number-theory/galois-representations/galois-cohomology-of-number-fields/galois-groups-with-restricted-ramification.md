# Galois groups with restricted ramification and their modules

Let $F$ be a number field and $S$ a set of places of $F$ containing the set $S_\infty$ of archimedean
places. Fix an algebraic closure $\bar F$. Let $F_S \subseteq \bar F$ be the maximal extension of $F$
unramified outside $S$ and $G_S = \operatorname{Gal}(F_S/F)$, a quotient of $G_F = \operatorname{Gal}(\bar F/F)$.
Let $\mathbb{N}(S)$ be the set of positive integers $n$ that are units in the ring
$\mathcal{O}_{F,S}$ of $S$-integers, that is, whose prime divisors $p$ satisfy $S_p \subseteq S$, where $S_p$
is the set of places above $p$.

- **Modules and global duals.** $\operatorname{Mod}_S(G_S)$ is the category of discrete $G_S$-modules $A$
  that are finitely generated as abelian groups and whose torsion subgroup has order in $\mathbb{N}(S)$. The
  **dual** of $A$ is the $G_S$-module $A' = \operatorname{Hom}(A, \mathcal{O}_S^\times)$, where
  $\mathcal{O}_S^\times$ is the group of $S$-units of $F_S$. For finite $A$ it is
  $A' = \operatorname{Hom}(A, \mu)$, with $\mu$ the roots of unity of $F_S$, since $F_S$ contains the $n$-th
  roots of unity for every $n \in \mathbb{N}(S)$.
- **Local groups.** For a place $v$ of $F$ let $F_v$ be the completion and fix an $F$-embedding
  $\bar F \to \bar F_v$; it identifies $G_v = \operatorname{Gal}(\bar F_v/F_v)$ with a decomposition group in
  $G_F$, and composing with $G_F \to G_S$ gives restriction maps $H^i(G_S, A) \to H^i(F_v, A) = H^i(G_v, A)$,
  independent of the embedding since conjugation acts trivially on cohomology. For the dual, the local
  group is taken for the dual in the local sense:

    $$H^i(F_v, A') = H^i\bigl(G_v, \operatorname{Hom}(A, \bar F_v^\times)\bigr),$$

    and $H^i(G_S, A') \to H^i(F_v, A')$ is restriction followed by the map induced by the inclusion
    $A' = \operatorname{Hom}(A, \mathcal{O}_S^\times) \hookrightarrow \operatorname{Hom}(A, \bar F_v^\times)$ of
    $G_v$-modules. For finite $A$ both readings of $H^i(F_v, A')$ agree; in general they do not: for
    $A = \mathbb{Z}$ and $v$ finite, $H^0(F_v, A') = F_v^\times$.

- **Unramified subgroups.** At a finite place $v$ at which $A$ is unramified,
  $H^i_{\mathrm{nr}}(F_v, A)$ is the image of $H^i(G_v/I_v, A^{I_v})$ in $H^i(F_v, A)$, where $I_v$ is the
  inertia group, and $H^i_{\mathrm{nr}}(F_v, A')$ is the image of $H^i(G_v/I_v, A^d)$ in $H^i(F_v, A')$, where
  $A^d = \operatorname{Hom}(A, \tilde{\mathcal{O}}_v^\times)$ and $\tilde{\mathcal{O}}_v$ is the ring of integers of
  the maximal unramified extension of $F_v$. For finite $A$ of order prime to the residue characteristic of $v$,
  $A^d = \operatorname{Hom}(A, \mu) = A'$.
- **Restricted products and localization.** For $M = A$ or $M = A'$ and $i \ge 0$, $P^i(G_S, M)$ is the
  restricted product of the groups $H^i(F_v, M)$, $v \in S$, with respect to the subgroups
  $H^i_{\mathrm{nr}}(F_v, M)$; for finite $S$ it is the product. In $P^0$ alone, the factor at an archimedean $v$
  is the Tate cohomology group $\hat H^0(F_v, M)$ instead of $H^0(F_v, M)$. Every class in $H^i(G_S, M)$ is
  unramified at almost all places of $S$, so restriction defines the **localization maps**
  $\lambda^i \colon H^i(G_S, M) \to P^i(G_S, M)$. The groups $H^i(F_v, M)$ are discrete except
  $H^0(F_v, A')$, which carries the topology of $\operatorname{Hom}(A, \bar F_v^\times)$.

## Depends on

- [Cohomology of a profinite group with discrete coefficients](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/cohomology-with-discrete-coefficients.md), for the cohomology of $G_S$ and of the decomposition groups
- [Unramified classes under local duality](../galois-cohomology-of-local-fields/unramified-classes-under-local-duality.md), for the unramified subgroups

## Proof depends on

- [Cyclotomic fields are unramified at primes not dividing $m$](../../cyclotomic-fields/ramification-and-inertia-in-cyclotomic-fields/is-unramified-in-of-not-dvd.md), applied to $\mathbb{Q}(\mu_n)$, so that $F(\mu_n) = F \cdot \mathbb{Q}(\mu_n)$ is unramified outside $S$ for $n \in \mathbb{N}(S)$
- [Cohomology as a direct limit over finite quotients](../../../../RepresentationTheory/group-cohomology/profinite-group-cohomology/discrete-coefficients/cohomology-as-a-direct-limit-over-finite-quotients.md), for the description of $H^i(G_S, M)$ as a direct limit of the cohomology of finite quotients, through which every class is inflated from a finite Galois extension unramified at almost all places

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: Chapter VIII, §3, p. 452 (the
  set $S \supseteq S_\infty$, $k_S$, $G_S$, $\mathbb{N}(S)$), (8.3.4) Proposition ($\mu_n \subseteq k_S$ for
  $n \in \mathbb{N}(S)$); §5, (8.5.1) Definition ($\operatorname{Mod}_S(G_S)$), the convention after (8.5.2) on
  p. 474 ($\hat H^0$ at archimedean primes in $P^0$) and p. 475 (the dual $A' = \operatorname{Hom}(A, \mathcal{O}_S^\times)$;
  "$H^i(k_\mathfrak{p}, A') \overset{\mathrm{def}}{=} H^i(k_\mathfrak{p}, \operatorname{Hom}(A, \bar k_\mathfrak{p}^\times))$";
  $H^i_{\mathrm{nr}}(k_\mathfrak{p}, A') = H^i_{\mathrm{nr}}(k_\mathfrak{p}, A^d)$ with
  $A^d = \operatorname{Hom}(A, \tilde{\mathcal{O}}_\mathfrak{p}^\times)$; the restricted products and their topologies);
  §6, (8.6.1) Proposition and its proof, and (8.6.2) Definition (the localization maps for $M = A$ and
  $M = A'$), pp. 480–481; Chapter VII, (7.2.14) Definition (unramified cohomology).
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, §4 (the groups $G_S$, $P^r_S(K, M)$ and the maps $\beta^r_S$ before Theorem 4.10).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  defines $G_S$ as `ReciprocityTheory.Gal.GS` and the restriction to decomposition groups as
  `ReciprocityTheory.Gal.locFam`.
