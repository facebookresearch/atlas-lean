# Relative roots, root space decompositions and root subgroups of reductive groups

This node is still to be broken down. It covers the relative root datum of a reductive group over a field that the
pages on buildings and Moy–Prasad filtrations use. Let $\mathbf{G}$ be a connected reductive group over a field $k$ with Lie
algebra $\mathfrak{g}$, and $S$ a maximal $k$-split torus.

- **Root space decomposition.** $S$ acts on $\mathfrak{g}$ through characters; the set $\Phi = \Phi(S, \mathbf{G})$ of nonzero
  characters that occur is the set of relative roots, and $\mathfrak{g} = \mathfrak{z}(S) \oplus \bigoplus_{a \in \Phi} \mathfrak{g}_a$, with
  $\mathfrak{z}(S)$ the Lie algebra of the centralizer of $S$.
- **Relative root system and Weyl group.** $\Phi$ is a root system, possibly non-reduced, in the subspace of $X^*(S) \otimes \mathbb{R}$
  that it spans, of rank the $k$-semisimple rank of $\mathbf{G}$, and the relative Weyl group $N(S)/Z(S)$ is finite and acts on it as
  its Weyl group. Maximal $k$-split tori are conjugate over $k$, and so are minimal parabolic $k$-subgroups.
- **Root subgroups.** For $a \in \Phi$ there is a unique connected unipotent $k$-subgroup $U_a$, normalized by $Z(S)$, with Lie
  algebra $\bigoplus_c \mathfrak{g}_{ca}$, the sum over the positive integers $c$ with $ca \in \Phi$.

## Expansion

A good expansion has definition pages for relative roots and root subgroups and statement pages for the root space
decomposition, for the conjugacy theorems and for the relative root system and Weyl group, each citing the source below
with locators.

A good expansion also writes out these steps of its own proof:

- the structure of minimal parabolic $k$-subgroups that Borel and Tits establish before the relative root system
  (their §4, through Theorem 4.13, Theorem 4.15 and Corollary 4.16), from which they derive the conjugacy of maximal $k$-split tori
  (Theorem 4.21) and, in §5, the relative root system.

## Depends on

- [Linear algebraic groups over local fields and their groups of rational points](../../RepresentationTheory/reductive-groups-over-local-fields/linear-algebraic-groups-over-local-fields.md), for the setting, connected reductive groups and split tori

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- A. Borel and J. Tits, "Groupes réductifs", Publ. Math. IHÉS 27 (1965), 55–150,
  <http://www.numdam.org/item?id=PMIHES_1965__27__55_0>: 3.2 (roots with respect to a torus), 3.8 (quasi-closed sets of roots
  and the associated unipotent subgroups), Theorem 4.13, p. 90 (minimal parabolic $k$-subgroups are conjugate over $k$),
  Theorem 4.21 (conjugacy of maximal $k$-split tori), and §5, 5.1–5.3, pp. 95–96 (the relative roots, the relative Weyl
  group, the root subgroups $U_{(a)}$, and Theorem 5.3: the rank of ${}_k\Phi$ is the $k$-semisimple rank, and ${}_kW$ is generated
  by the reflections in the hyperplanes of the $k$-roots), with Corollary 5.8, p. 98 (${}_k\Phi$ is a root system).
