# Serre–Tate theorem

This node is still to be broken down: the statement is precise, and the proof is outlined below; its
inputs remain to be separated.

Let $p$ be a prime, $R$ a ring in which $p$ is nilpotent, $I \subset R$ a nilpotent ideal and $R_0 =
R/I$. Let $\mathrm{AV}_R$ be the category of [abelian schemes](../abelian-scheme.md) over $R$, and
$\mathrm{AVBT}_{R_0, R}$ the category of triples $(A_0, X, \varepsilon)$ of an abelian scheme $A_0$
over $R_0$, a [$p$-divisible group](p-divisible-group.md) $X$ over $R$ and an isomorphism of
$p$-divisible groups $\varepsilon \colon X \times_R R_0 \to A_0[p^\infty]$; a morphism $(A_0, X,
\varepsilon) \to (A'_0, X', \varepsilon')$ is a pair of a homomorphism $h_0 \colon A_0 \to A'_0$ and
a homomorphism $f \colon X \to X'$ with $h_0[p^\infty] \circ \varepsilon = \varepsilon' \circ (f
\times_R R_0)$.

**Theorem** (Serre–Tate). The functor $\mathrm{AV}_R \to \mathrm{AVBT}_{R_0, R}$ sending an abelian
scheme $A$ to $(A \times_R R_0,\ A[p^\infty],\ \mathrm{can})$, with $\mathrm{can} \colon A[p^\infty]
\times_R R_0 \cong (A \times_R R_0)[p^\infty]$ the canonical isomorphism, is an equivalence of
categories.

No coherence condition on $I$ is needed (Katz, Theorem 1.2.1). Chai and Oort state the theorem for a
scheme $S$ on which $p$ is locally nilpotent and a coherent, locally nilpotent ideal sheaf
$\mathcal{I} \subset \mathcal{O}_S$; that form follows by working locally on $S$ and gluing. Both
categories allow abelian schemes of any relative dimension, a locally constant function, and
$p$-divisible groups of any locally constant height. In words, deforming an abelian scheme over a
nilpotent thickening on which $p$ is nilpotent is the same as deforming its $p$-divisible group;
Chai and Oort deduce that the deformation functor of an abelian variety over a perfect field of
characteristic $p$ is equivalent to that of its $p$-divisible group.

Katz gives Drinfeld's proof. Let $N$ be an integer killing $R$, a power of $p$, and $I^{\nu+1} = 0$.
For a commutative formal Lie group $G$ the kernel $G_I$ of $G(A) \to G(A/IA)$ is killed by $N^\nu$
(Lemmas 1.1.1–1.1.2). Hence, for fppf abelian sheaves $G$, $H$ with $G$ $N$-divisible and $H$
formally smooth and locally a formal Lie group, and for a homomorphism $f_0 \colon G_0 \to H_0$ over
$R_0$, there is a unique homomorphism "$N^\nu f$" $\colon G \to H$ lifting $N^\nu f_0$, not $f_0$
itself (it is $N^\nu$ times any local lift of $f_0$); and $f_0$ lifts, necessarily uniquely, if and
only if "$N^\nu f$" kills $G[N^\nu]$ (Lemma 1.1.3 (3)–(4)). Full faithfulness follows by applying
this to $A$, $B$ and to their $p$-divisible groups. For essential surjectivity, given $(A_0, X,
\varepsilon)$, Katz first chooses an abelian scheme $B$ over $R$ lifting $A_0$, which exists because
$R$ is a nilpotent thickening of $R_0$; the canonical lift of $N^\nu \varepsilon^{-1}$ is an isogeny
$B[p^\infty] \to X$ with kernel $K \subset B[N^{2\nu}]$, finite and flat by the fibrewise criterion
of flatness; and $A = B/K$, the quotient of $B$ by the finite flat subgroup $K$, is the required
lift (pp. 144–146).

A good expansion has pages for the three inputs of this proof that the linked pages do not supply:
Katz's Lemmas 1.1.1–1.1.3 on lifting homomorphisms of fppf sheaves; the existence of an abelian
scheme over $R$ lifting a given abelian scheme over $R_0$, along a nilpotent thickening of an affine
base (Grothendieck's deformation theory of smooth group schemes, which Katz uses without proof); and
the existence of the quotient of an abelian scheme by a finite flat subgroup scheme as an abelian
scheme (Robert, Proposition 2.3.15, through Raynaud's theorem on abelian algebraic spaces or the
existence of quotients of AF-schemes).

## Depends on

- [Abelian scheme](../abelian-scheme.md)
- [p-divisible group](p-divisible-group.md)

## Proof depends on

- [Isogenies of abelian schemes](../isogenies-of-abelian-schemes.md), for multiplication by an integer
  as a finite flat epimorphism and the finite flat kernels $A[p^n]$
- [Homomorphisms of abelian schemes and commutativity](../homomorphisms-of-abelian-schemes.md), for the
  morphisms of abelian schemes that preserve the zero section

## Sources

- N. M. Katz, "Serre–Tate local moduli", in *Surfaces algébriques* (J. Giraud, L. Illusie and M.
  Raynaud, eds.), Lecture Notes in Mathematics 868, Springer, 1981, 138–202: §1, Drinfeld's proof,
  Lemmas 1.1.1–1.1.3, and Theorem 1.2.1 with its proof, pp. 141–147.
- D. Robert, *Theory of abelian varieties and their moduli spaces*, draft book (version of 7 March
  2023), <https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/books/avtheory.pdf>:
  Proposition 2.3.15 and its proof (quotients by finite flat subgroups), pp. 16–17.
- C.-L. Chai and F. Oort, "Moduli of abelian varieties and p-divisible groups: density of Hecke
  orbits, and a conjecture of Grothendieck", lecture notes, arXiv:math/0701479 (version 1): (2.6)
  (the setting) and Theorem 2.7 (Serre–Tate), with the remark after it (the theorem goes back to
  Lubin–Serre–Tate; a proof first appeared in print in Messing's book; see also Katz), and Corollary
  2.8.
- W. Messing, *The Crystals Associated to Barsotti–Tate Groups: with Applications to Abelian
  Schemes*, Lecture Notes in Mathematics 264, Springer, 1972, chapter "The deformation theory and
  applications" (pp. 150–174).
