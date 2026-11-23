# Poitou–Tate duality

Let $F$ be a number field, $S \supseteq S_\infty$ a set of places of $F$ (finite or not), $G_S$ the Galois
group of the maximal extension of $F$ unramified outside $S$, and $A$ a $G_S$-module that is finitely
generated as an abelian group with torsion of order in $\mathbb{N}(S)$, with dual
$A' = \operatorname{Hom}(A, \mathcal{O}_S^\times)$. Here $\text{Ш}^1(G_S, A')$ is the kernel of the localization
map of $A'$, whose local components are taken in the local duals
$H^1(F_v, \operatorname{Hom}(A, \bar F_v^\times))$. Then $\text{Ш}^1(G_S, A')$ and $\text{Ш}^2(G_S, A)$ are
finite and there is a perfect pairing

$$\text{Ш}^1(G_S, A') \times \text{Ш}^2(G_S, A) \to \mathbb{Q}/\mathbb{Z},$$

induced by the cup product $H^0(G_S, C_S(A)) \times H^2(G_S, A) \to H^2(G_S, C_S) \to \mathbb{Q}/\mathbb{Z}$ of the
$S$-idèle class formation. If $A$ is finite, interchanging $A$ and $A' $ gives a perfect pairing
$\text{Ш}^1(G_S, A) \times \text{Ш}^2(G_S, A') \to \mathbb{Q}/\mathbb{Z}$ as well; in particular
$\# \text{Ш}^1(G_S, A) = \# \text{Ш}^2(G_S, A')$.

## Depends on

- [Tate–Shafarevich groups of Galois modules](tate-shafarevich-groups.md)
- [Galois groups with restricted ramification and their modules](galois-groups-with-restricted-ramification.md), for $\operatorname{Mod}_S(G_S)$ and the dual $A'$

## Proof depends on

- [Global duality for Galois groups with restricted ramification](global-duality-for-galois-groups-with-restricted-ramification.md), for the global duality theorem, the Shapiro maps and the boundary map $C_S(A)^{G_S} \to H^1(G_S, A')$ (NSW (8.4.4), (8.4.5), (8.5.5), (8.6.4)–(8.6.6))
- [Local Tate duality](../galois-cohomology-of-local-fields/local-tate-duality.md)

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: (8.6.7) Theorem (Poitou–Tate
  duality, for $A$ finitely generated with $\# \mathrm{tor}(A) \in \mathbb{N}(S)$) and its proof, pp. 485–486;
  the paragraph after (8.6.8) (for finite $A$, $A$ and $A'$ may be interchanged), p. 488.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Theorem 4.10 (a) (finite $M$).
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the equality of orders, for finite $S$ containing the places above $\ell \ne 2$, as
  `ReciprocityTheory.Gal.ShaDuality`, and inside `GlobalTheory.Published.PoitouTateNormalised`.
