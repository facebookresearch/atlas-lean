# Serre–Tate theorem

Let $p$ be a prime, $S$ a scheme on which $p$ is locally nilpotent, $\mathcal{I} \subset \mathcal{O}_S$
a coherent sheaf of ideals that is locally nilpotent, and $S_0 \subset S$ the closed subscheme it
defines. Let $\mathrm{AV}_S$ be the category of [abelian schemes](abelian-scheme.md) over $S$, and
$\mathrm{AVBT}_{S_0, S}$ the category of triples $(A_0, X, \varepsilon)$ of an abelian scheme $A_0$
over $S_0$, a [$p$-divisible group](p-divisible-group.md) $X$ over $S$ and an isomorphism of
$p$-divisible groups $\varepsilon \colon X \times_S S_0 \to A_0[p^\infty]$; a morphism
$(A_0, X, \varepsilon) \to (A'_0, X', \varepsilon')$ is a pair of a homomorphism
$h_0 \colon A_0 \to A'_0$ and a homomorphism $f \colon X \to X'$ with
$h_0[p^\infty] \circ \varepsilon = \varepsilon' \circ (f \times_S S_0)$.

**Theorem** (Serre–Tate). The functor $\mathrm{AV}_S \to \mathrm{AVBT}_{S_0, S}$ sending an abelian
scheme $A$ to $(A \times_S S_0,\ A[p^\infty],\ \mathrm{can})$, with
$\mathrm{can} \colon A[p^\infty] \times_S S_0 \cong (A \times_S S_0)[p^\infty]$ the canonical
isomorphism, is an equivalence of categories.

In words, deforming an abelian scheme over a nilpotent thickening on which $p$ is nilpotent is the
same as deforming its $p$-divisible group; Chai and Oort deduce that the deformation functor of an
abelian variety over a perfect field of characteristic $p$ is equivalent to that of its $p$-divisible
group.

## Depends on

- [Abelian scheme](abelian-scheme.md)
- [p-divisible group](p-divisible-group.md)

## Proof depends on

- [Grothendieck–Messing deformation theorem](grothendieck-messing-theorem.md), for Messing's
  deformation theory of $p$-divisible groups, within which he proves the theorem

## Sources

- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): (2.6)
  (the setting) and Theorem 2.7 (Serre–Tate), with the remark after it (the theorem goes back to
  Lubin–Serre–Tate; a proof first appeared in print in Messing's book; see also Katz), and
  Corollary 2.8.
- W. Messing, *The Crystals Associated to Barsotti–Tate Groups: with Applications to Abelian Schemes*,
  Lecture Notes in Mathematics 264, Springer, 1972, chapter "The deformation theory and applications"
  (pp. 150–174).
- N. M. Katz, "Appendix to Exposé V", in *Surfaces algébriques* (J. Giraud, L. Illusie and
  M. Raynaud, eds.), Lecture Notes in Mathematics 868, Springer, 1981, 127–137, as cited by
  Chai–Oort; and J. Lubin, J.-P. Serre and J. Tate, *Elliptic curves and formal groups*, notes of the
  Woods Hole Summer Institute, 1964.
