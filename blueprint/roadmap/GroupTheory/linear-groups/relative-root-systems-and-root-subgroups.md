# Relative roots, root space decompositions and root subgroups of reductive groups

This node is still to be broken down. It covers the relative root datum of a reductive group over a field that the
pages on buildings and Moy–Prasad filtrations use. Let $\mathbf{G}$ be a connected reductive group over a field $k$ with Lie
algebra $\mathfrak{g}$, and $S$ a maximal $k$-split torus.

- **Root space decomposition.** $S$ acts on $\mathfrak{g}$ through characters; the set $\Phi = \Phi(S, \mathbf{G})$ of nonzero
  characters that occur is the set of relative roots, and $\mathfrak{g} = \mathfrak{z}(S) \oplus \bigoplus_{a \in \Phi} \mathfrak{g}_a$, with
  $\mathfrak{z}(S)$ the Lie algebra of the centralizer of $S$.
- **Relative root system and Weyl group.** $\Phi$ is a root system, possibly non-reduced, in the subspace of $X^*(S) \otimes \mathbb{R}$
  that it spans, of rank the $k$-semisimple rank of $\mathbf{G}$, and the relative Weyl group $N(S)/Z(S)$ is finite and acts on it as
  its Weyl group. Maximal $k$-split tori are conjugate over $k$.
- **Root subgroups.** For $a \in \Phi$ there is a unique connected unipotent $k$-subgroup $U_a$, normalized by $Z(S)$, with Lie
  algebra $\bigoplus_c \mathfrak{g}_{ca}$, the sum over the positive integers $c$ with $ca \in \Phi$.

## Expansion

A good expansion has definition pages for relative roots and root subgroups and statement pages for the root space
decomposition and for the relative root system and Weyl group, each citing the source below with locators.

## Depends on

- [Linear algebraic groups over local fields and their groups of rational points](../../RepresentationTheory/reductive-groups-over-local-fields/linear-algebraic-groups-over-local-fields.md), for the setting
- [Parabolic subgroups and the rational Bruhat decomposition of reductive groups](parabolic-subgroups-and-rational-bruhat-decomposition.md), for maximal split tori and
  minimal parabolic subgroups

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- A. Borel and J. Tits, "Groupes réductifs", Publ. Math. IHÉS 27 (1965), 55–150,
  <http://www.numdam.org/item?id=PMIHES_1965__27__55_0>: 3.2 (roots with respect to a torus), 3.8 (quasi-closed sets of roots
  and the associated unipotent subgroups), 4.21 (conjugacy of maximal $k$-split tori), and §5, 5.1–5.3, pp. 95–96 (the relative
  roots, the relative Weyl group, the root subgroups $U_{(a)}$, and Theorem 5.3: ${}_k\Phi$ is a root system of rank the
  $k$-semisimple rank).
