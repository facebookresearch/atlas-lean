# Hilbert's tenth problem is undecidable for function fields over real and p-adic fields

Let $K$ be the function field of a smooth irreducible positive-dimensional variety over a field of characteristic zero. If $K$ is formally real, or if the constant field embeds in a finite extension of $\mathbb{Q}_p$ for an odd prime $p$, then the positive-existential theory of $K$ is undecidable, so Hilbert's tenth problem over $K$ has a negative answer.

Let $k$ be a field of characteristic zero and $V$ a smooth, positive-dimensional, quasiprojective, irreducible $k$-scheme with function field $K$. A field is *formally real* when $-1$ is not a sum of squares in it. The *positive-existential theory* of a ring $A$ is the set of true sentences $\exists x_1 \cdots \exists x_n \, \theta$ with $\theta$ built from equations by conjunction and disjunction; the source calls its undecidability a negative solution of Hilbert's tenth problem over $A$.

**Theorem (Moret-Bailly).**

1. Let $Q$ be a nonempty effective divisor on $V$ and let $A \subset K$ be the semilocal ring of $Q$, the intersection of the local rings at the maximal points of $Q$. Then the positive-existential theory of $A$ is undecidable: Hilbert's tenth problem over $A$ has a negative answer.
2. If $K$ is formally real, then the positive-existential theory of $K$ is undecidable.
3. If $k$ is a subfield of a finite extension of $\mathbb{Q}_p$ for some odd prime $p$, then the positive-existential theory of $K$ is undecidable.

In particular, in cases 2 and 3 there is no algorithm that takes a polynomial $F \in K[X_1, \dots, X_n]$ (from the admissible countable set of inputs) and decides whether $F$ has a zero in $K^n$. Conventions: in all three statements the positive-existential theory is taken in the language of rings augmented by a suitable set of constants, which the source says can be described explicitly.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Field](../../../Algebra/rings-and-fields/field.md)
- [The field of p-adic numbers](../../p-adic-numbers/p-adic-numbers.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

In each case the source builds a Diophantine (positive-existentially definable) subset of $A^d$ or $K^d$, with $d = 2$ in cases 1 and 2, carrying a Diophantine ring structure isomorphic to $\mathbb{Z}$; undecidability over $\mathbb{Z}$ then transfers. By enlarging $k$ one may assume in cases 1 and 2 that $V$ is a smooth projective geometrically connected curve. The construction follows Denef's method for $k(t)$ with $k$ real: it uses elliptic curves over $K$ whose groups of points have rank one, obtained as specializations of a family of curves, and the main new input is a theorem describing the parameters with the required behavior: they include every element transcendental over $k$ and, when $k$ is finitely generated over the prime field, a Hilbert subset of $k$. Case 3 adapts the argument of Kim and Roush for $k(t)$ with $k$ $p$-adic, which is the source of the restriction $p \neq 2$. Earlier special cases include Denef's theorem for $k(t)$ with $k$ formally real. A good expansion links pages for Moret-Bailly's specialization theorem for families of elliptic curves, for Denef's method for $k(t)$ with $k$ real, for the Kim–Roush argument over $p$-adic fields, and for the transfer of undecidability along a Diophantine model of $\mathbb{Z}$.

## Sources

- Laurent Moret-Bailly, *Elliptic curves and Hilbert's tenth problem for algebraic function fields over real and $p$-adic fields*, J. Reine Angew. Math. 587 (2005), 77–143, https://doi.org/10.1515/crll.2005.2005.587.77; Theorem 1.1 of arXiv:math/0409103v3 with Remarks 1.1.1 to 1.1.3, its parts being proved as Theorems 10.3, 11.2 and 12.1 there.
- Kirsten Eisenträger (Eisentraeger), *Hilbert's tenth problem for function fields of characteristic zero*, in: Model Theory with Applications to Algebra and Analysis, Cambridge University Press, 2008, pp. 237–254, https://doi.org/10.1017/CBO9780511735219.008, which presents Denef's theorem for $k(t)$ with $k$ formally real (Theorem 3.1 of arXiv:math/0610162v1).
