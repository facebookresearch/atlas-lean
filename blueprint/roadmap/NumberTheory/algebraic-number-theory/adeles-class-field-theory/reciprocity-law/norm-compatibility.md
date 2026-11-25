# Norm compatibility of the global Artin map

Let $K'/K$ be a finite extension of number fields inside a fixed algebraic closure, so that
$K^{\mathrm{ab}} \subseteq K'^{\mathrm{ab}}$, and let $\mathrm{Nm}_{K'/K} \colon \mathbb{I}_{K'} \to \mathbb{I}_K$
be the idèle norm, $\mathrm{Nm}_{K'/K}(b)_v = \prod_{w \mid v} \mathrm{Nm}_{K'_w/K_v}(b_w)$. Then the
[global Artin maps](global-artin-map.md) satisfy

$$\phi_{K'}(b)|_{K^{\mathrm{ab}}} = \phi_K(\mathrm{Nm}_{K'/K}(b)) \qquad (b \in \mathbb{I}_{K'}).$$

Equivalently, for every finite abelian extension $L/K$, $\phi_{LK'/K'}(b)|_L = \phi_{L/K}(\mathrm{Nm}_{K'/K}(b))$.
In particular, if $K \subseteq K' \subseteq L$ with $L/K$ finite abelian, then
$\phi_{L/K}(\mathrm{Nm}_{K'/K}(b)) = \phi_{L/K'}(b)$ in $\mathrm{Gal}(L/K') \subseteq \mathrm{Gal}(L/K)$; taking
$K' = L$, the norm group $\mathrm{Nm}_{L/K}(\mathbb{I}_L)$ lies in the kernel of $\phi_{L/K}$.

The idèle norm is compatible with the embeddings of the local groups:
$\mathrm{Nm}_{K'/K}(\iota_w(y)) = \iota_v(\mathrm{Nm}_{K'_w/K_v}(y))$ for $y \in K'^\times_w$, $w \mid v$. Since
both sides of the formula are continuous homomorphisms, it therefore suffices to compare them on the
local groups, where it is the compatibility of the local Artin maps with norms: for a finite extension
$K'_w/K_v$ of local fields and $y \in K'^\times_w$, the local Artin map of $K'_w$ at $y$, restricted to the
maximal abelian extension of $K_v$, is the local Artin map of $K_v$ at $\mathrm{Nm}_{K'_w/K_v}(y)$ (at an
archimedean place this is immediate).

## Depends on

- [Global Artin map](global-artin-map.md)

## Proof depends on

- [Local class field theory: functoriality and explicit reciprocity](../../../p-adic-numbers/local-class-field-theory-functoriality.md), for the compatibility of the local Artin maps with norms (its item 1)

## Sources

- J. S. Milne, *Class Field Theory*, version 4.03 (2020),
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>: the proof of Proposition V.5.2 (the case
  $K \subseteq K' \subseteq L \subseteq K^{\mathrm{ab}}$ and the norms in the kernel) and the proof of Lemma
  VII.8.4(b) (the case $L' = LK'$, from the local diagrams).
- A. V. Sutherland, *Number Theory I* (MIT 18.785, Fall 2021), Lecture 28,
  <https://math.mit.edu/classes/18.785/2021fa/LectureNotes28.pdf>: the diagram for $\iota_w$, $\iota_v$
  and the norms in Section 28.2, and Theorem 28.8 (functoriality).
