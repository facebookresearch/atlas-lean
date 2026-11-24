# Poitou–Tate exact sequence

Let $F$ be a number field, $S \supseteq S_\infty$ a set of places of $F$, $G_S$ the Galois group of the
maximal extension of $F$ unramified outside $S$, and $A$ a finite $G_S$-module of order in $\mathbb{N}(S)$
with dual $A' = \operatorname{Hom}(A, \mu)$. There is a canonical exact sequence of topological groups

$$
\begin{array}{ccccccccc}
0 \to & H^0(G_S, A) & \xrightarrow{\lambda^0} & P^0(G_S, A) & \to & H^2(G_S, A')^\vee & \to \\
      & H^1(G_S, A) & \xrightarrow{\lambda^1} & P^1(G_S, A) & \to & H^1(G_S, A')^\vee & \to \\
      & H^2(G_S, A) & \xrightarrow{\lambda^2} & P^2(G_S, A) & \to & H^0(G_S, A')^\vee & \to 0.
\end{array}
$$

Here $\lambda^i$ are the localization maps into the restricted products $P^i(G_S, A)$, with Tate cohomology
$\hat H^0$ at the archimedean places in $P^0$, and $^\vee$ is the Pontryagin dual. Each map
$P^i(G_S, A) \to H^{2-i}(G_S, A')^\vee$ is the composite of an isomorphism
$P^i(G_S, A) \cong P^{2-i}(G_S, A')^\vee$ with the dual of the localization map $\lambda^{2-i}$ for $A'$. That
isomorphism of restricted products is induced by local Tate duality at the finite places and Tate duality for
$\mathbb{R}$ at the real places, because at the finite places where $A$ is unramified and of order prime to the
residue characteristic the unramified subgroups of $H^i(F_v, A)$ and $H^{2-i}(F_v, A')$ are exact annihilators of
each other. The maps $H^{2-i}(G_S, A')^\vee \to H^{i+1}(G_S, A)$ for $i = 0, 1$ have images
$\text{Ш}^{i+1}(G_S, A)$ and are induced by the Poitou–Tate duality pairings. The groups $H^0(G_S, A)$,
$H^0(G_S, A')^\vee$ are finite, $P^0$, $H^2(G_S, A')^\vee$ and $H^1(G_S, A')^\vee$ are compact, $P^1$ is locally
compact, and $H^1(G_S, A)$, $P^2$ and $H^2(G_S, A)$ are discrete. If $S$ is finite, all the groups are finite.

## Depends on

- [Galois groups with restricted ramification and their modules](galois-groups-with-restricted-ramification.md), for the localization maps and the restricted products $P^i$
- [Local Tate duality](../galois-cohomology-of-local-fields/local-tate-duality.md), for the identification $P^i(G_S, A) \cong P^{2-i}(G_S, A')^\vee$ at the non-archimedean places
- [Tate duality for the real numbers](../galois-cohomology-of-local-fields/tate-duality-for-the-real-numbers.md), for the archimedean places
- [Unramified classes under local duality](../galois-cohomology-of-local-fields/unramified-classes-under-local-duality.md), for the unramified subgroups as exact annihilators in degrees $0$, $1$ and $2$, which make the local dualities an isomorphism of restricted products
- [Poitou–Tate duality](poitou-tate-duality.md), for the maps $H^{2-i}(G_S, A')^\vee \to H^{i+1}(G_S, A)$

## Proof depends on

- [Poitou–Tate duality](poitou-tate-duality.md)
- [Exactness of the Poitou–Tate complex](exactness-of-the-poitou-tate-complex.md), for the reduction steps of NSW's proof: the base cases $\mathbb{Z}/p\mathbb{Z}$ and $\mu_p$, the properness of $\lambda^1$, the sequence (8.6.12) and the exactness criterion (8.6.13)
- [Global duality for Galois groups with restricted ramification](global-duality-for-galois-groups-with-restricted-ramification.md), for the global duality theorem and the Shapiro maps
- [Finiteness and cohomological dimension of Galois groups with restricted ramification](finiteness-and-cohomological-dimension-of-g-s.md), for the finiteness when $S$ is finite

## Sources

- J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., electronic edition,
  version 2.3 (May 2020), <https://www.mathi.uni-heidelberg.de/~schmidt/NSW2e/>: (8.6.10) Long Exact Sequence
  of Poitou–Tate (i), with the Remark after it (the nine terms in three rows) and its proof through (8.6.11)–(8.6.13),
  pp. 489–499; (8.5.2) Proposition (the isomorphisms $\Xi^i \colon P^i(G_S, A) \cong P^{2-i}(G_S, A')^\vee$, from
  (7.2.9) and (7.2.15)), p. 474.
- J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., 2006, <https://www.jmilne.org/math/Books/ADTnot.pdf>:
  Chapter I, Theorem 4.10 (b) and the exact sequence after it, with the table of topological properties.
- Provenance: L. Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>)
  uses the sequence, for finite $S$ containing the places above $\ell$ with $\ell \ne 2$ or $F$ totally
  complex and local invariant maps normalized by a cup-product condition, as
  `GlobalTheory.Published.PoitouTateNormalised`, and the length identities derived from it as
  `Formalism.GaloisCohomology.PTCoker` and `PTSha`.
