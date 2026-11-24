# Tate–Shafarevich groups of Galois modules

Let $F$ be a number field, $S \supseteq S_\infty$ a set of places of $F$, $G_S$ the Galois group of the
maximal extension of $F$ unramified outside $S$, and $A$ a discrete $G_S$-module. For $i \ge 0$ the
**Tate–Shafarevich group** of $A$ in degree $i$ is the kernel of localization at the places of $S$:

$$\text{Ш}^i(G_S, A) = \ker\Bigl(H^i(G_S, A) \to \prod_{v \in S} H^i(F_v, A)\Bigr),$$

with the restriction maps to decomposition groups $G_v \subseteq G_F$ and, for archimedean $v$ and $i = 0$,
Tate cohomology $\hat H^0(F_v, A)$. For $A \in \operatorname{Mod}_S(G_S)$ it is the kernel of the
localization map $\lambda^i \colon H^i(G_S, A) \to P^i(G_S, A)$. For the dual
$A' = \operatorname{Hom}(A, \mathcal{O}_S^\times)$ of such an $A$, the local groups are those of the dual in the
local sense, $H^i(F_v, A') = H^i(G_v, \operatorname{Hom}(A, \bar F_v^\times))$, reached by restriction followed by
the inclusion $A' \hookrightarrow \operatorname{Hom}(A, \bar F_v^\times)$; so
$\text{Ш}^i(G_S, A') = \ker(\lambda^i \colon H^i(G_S, A') \to P^i(G_S, A'))$. For finite $A$ this agrees with
the definition above applied to the discrete module $A' = \operatorname{Hom}(A, \mu)$.

For $i \ge 1$ the factor of a complex place $v$ vanishes, since $G_v$ is trivial; so when $F$ is totally
imaginary, $\text{Ш}^i(G_S, A)$ for $i \ge 1$ is the kernel of localization at the non-archimedean places of
$S$ alone. For instance, if $S$ consists of the archimedean places and the places above a prime $\ell$, and
$A = \mathbb{Q}_\ell/\mathbb{Z}_\ell(i)$, then $\text{Ш}^1(G_S, \mathbb{Q}_\ell/\mathbb{Z}_\ell(i))$ is the kernel
of $H^1(G_S, \mathbb{Q}_\ell/\mathbb{Z}_\ell(i)) \to \prod_{v \mid \ell} H^1(F_v, \mathbb{Q}_\ell/\mathbb{Z}_\ell(i))$
when $F$ is totally imaginary.

## Depends on

- [Galois groups with restricted ramification and their modules](galois-groups-with-restricted-ramification.md), for $G_S$, the localization maps and $P^i(G_S, A)$
- [Cyclotomic character and Tate twists](../cyclotomic-character-and-tate-twists.md), for the twists $\mathbb{Q}_\ell/\mathbb{Z}_\ell(i)$ in the example

## Proof depends on

- [Galois groups with restricted ramification and their modules](galois-groups-with-restricted-ramification.md), for $A' = \operatorname{Hom}(A, \mu)$ for finite $A$ and the agreement, for finite $A$, of the two readings of $H^i(F_v, A')$, which give the last assertion of the first paragraph

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: (8.6.2) Definition
  ($\text{Ш}^i(G_S, M) = \ker(\lambda^i)$, for $M = A$ or $A'$ with $A \in \operatorname{Mod}_S(G_S)$, and the
  footnote on the name), p. 481.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, §4, the definition of $\text{Ш}^r_S(K, M)$ before Theorem 4.10.
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses $\text{Ш}^1$ of $\mathbb{Q}_\ell/\mathbb{Z}_\ell(-e)$, with localization at the places above $\ell$ only,
  as `Formalism.GaloisCohomology.Sha`, and its $\mathbb{Z}_\ell$-length as `shaLen`.
