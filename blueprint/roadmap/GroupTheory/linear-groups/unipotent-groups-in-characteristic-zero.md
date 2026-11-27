# Unipotent groups in characteristic zero: central series, exponential map and sections

This node is still to be broken down. It covers the structure of unipotent algebraic groups over a field of
characteristic zero that the compactness of unipotent adelic quotients uses. Let $k$ be a field of characteristic zero. An
algebraic group over $k$ is unipotent if it is isomorphic to an algebraic subgroup of the group $U_n$ of upper unitriangular
$n \times n$ matrices for some $n$. Let $N$ be a unipotent algebraic group over $k$ with Lie algebra $\mathfrak{n}$.

- **Central series.** $N$ has a central normal series by normal $k$-subgroups whose successive quotients are isomorphic to the
  additive group $\mathbb{G}_a$; in particular $N$ is split over $k$ and isomorphic as a $k$-variety to affine space.
- **Exponential map.** $\exp \colon \mathfrak{n} \to N$ is an isomorphism of $k$-schemes, with
  $g \exp(X) g^{-1} = \exp(\mathrm{Ad}(g)X)$, and an isomorphism of algebraic groups when $N$ is commutative; it commutes with
  homomorphisms.
- **Sections.** For a normal $k$-subgroup $N'$ with quotient $\pi \colon N \to N'' = N/N'$, there is a morphism of
  $k$-varieties $s \colon N'' \to N$, defined everywhere, with $\pi \circ s = \mathrm{id}$; hence $N(R) \to N''(R)$ is surjective for
  every $k$-algebra $R$, and $N \cong N' \times N''$ as $k$-varieties.

## Expansion

A good expansion has statement pages for the central series, for the exponential map and for the sections, each citing the
source below with locators. The section is $s = \exp \circ \sigma \circ \exp^{-1}$ for a linear section $\sigma$ of
$d\pi \colon \mathfrak{n} \to \mathfrak{n}''$: then $\pi \circ s = \exp \circ\, d\pi \circ \sigma \circ \exp^{-1} = \mathrm{id}$, since the
exponential commutes with $\pi$.

## Depends on

- [Linear algebraic groups over local fields and their groups of rational points](../../RepresentationTheory/reductive-groups-over-local-fields/linear-algebraic-groups-over-local-fields.md), for linear algebraic groups over a field and their algebraic subgroups

## Proof depends on

Its proof is that of the sources below, as the Expansion describes.

## Sources

- J. S. Milne, *Algebraic Groups* (version 2.00, 20 December 2015), <https://www.jmilne.org/math/CourseNotes/iAG200.pdf>:
  3.28, p. 61 (unipotent group varieties, isomorphic to subgroup varieties of $U_n$; split ones, with a subnormal series
  with quotients $\mathbb{G}_a$, are isomorphic to affine space), Proposition 15.23 (a central normal series with quotients
  algebraic subgroups of $\mathbb{G}_a$) and Remark 15.26 (a) (in characteristic zero these are $e$ and $\mathbb{G}_a$), pp. 256–257,
  and §15.c, pp. 258–259 (Lemma 15.30, the exponential map and $g \exp(X) g^{-1} = \exp(\mathrm{Ad}(g)(X))$, Proposition 15.31,
  an isomorphism of algebraic groups from the Lie algebra in the commutative case, with its proof through the central
  normal series, and Corollary 15.32).
- A. Borel and J. Tits, "Groupes réductifs", Publ. Math. IHÉS 27 (1965), 55–150,
  <http://www.numdam.org/item?id=PMIHES_1965__27__55_0>: 2.7, p. 67 ($k$-split solvable groups, and every homogeneous
  $k$-space of such a group has a $k$-rational point, after Rosenlicht).
