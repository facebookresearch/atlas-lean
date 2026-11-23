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

Both categories allow abelian schemes of any relative dimension, a locally constant function on $S$,
and $p$-divisible groups of any locally constant height. In words, deforming an abelian scheme over a
nilpotent thickening on which $p$ is nilpotent is the same as deforming its $p$-divisible group; Chai
and Oort deduce that the deformation functor of an abelian variety over a perfect field of
characteristic $p$ is equivalent to that of its $p$-divisible group.

Katz gives Drinfeld's proof, for $S = \operatorname{Spec} R$ with $p$ nilpotent in $R$ and $I$ a
nilpotent ideal; the general case follows by working locally on $S$ and gluing. If $p^N = 0$ in $R$ and
$I^{\nu + 1} = 0$, the kernel of $G(R) \to G(R/I)$ is killed by $p^{N\nu}$ for every formal Lie group
$G$; so for abelian schemes $A$, $B$ over $R$, a homomorphism $f_0 \colon A_0 \to B_0$ has a unique
"lift" $p^{N\nu} f$ to a homomorphism of fppf sheaves, defined as $p^{N\nu}$ times an arbitrary local
lift of $f_0$. Using that multiplication by $p^{N\nu}$ is an epimorphism of fppf sheaves with finite
flat kernel, Drinfeld deduces full faithfulness, and then essential surjectivity by a quotient
construction.

## Depends on

- [Abelian scheme](abelian-scheme.md)
- [p-divisible group](p-divisible-group.md)

## Proof depends on

- [Isogenies of abelian schemes](isogenies-of-abelian-schemes.md), for multiplication by an integer
  as a finite flat epimorphism and the finite flat kernels $A[p^n]$
- [Homomorphisms of abelian schemes and commutativity](homomorphisms-of-abelian-schemes.md), for the
  morphisms of abelian schemes that preserve the zero section

## Sources

- N. M. Katz, "Serre–Tate local moduli", in *Surfaces algébriques* (J. Giraud, L. Illusie and
  M. Raynaud, eds.), Lecture Notes in Mathematics 868, Springer, 1981, 138–202: §1, Drinfeld's proof,
  Lemma 1.1.1 and the lemmas of §1.1, and Theorem 1.2.1 with its proof, pp. 141–147.
- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): (2.6)
  (the setting) and Theorem 2.7 (Serre–Tate), with the remark after it (the theorem goes back to
  Lubin–Serre–Tate; a proof first appeared in print in Messing's book; see also Katz), and
  Corollary 2.8.
- W. Messing, *The Crystals Associated to Barsotti–Tate Groups: with Applications to Abelian Schemes*,
  Lecture Notes in Mathematics 264, Springer, 1972, chapter "The deformation theory and applications"
  (pp. 150–174).
