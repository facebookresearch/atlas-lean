# Hilbert's tenth problem is undecidable over every infinite finitely generated ring

For every number field $K$, the integers form a Diophantine subset of the ring of integers $\mathcal{O}_K$, so Hilbert's tenth problem over $\mathcal{O}_K$ is undecidable; consequently Hilbert's tenth problem is undecidable over every finitely generated commutative ring of infinite cardinality.

A *finitely generated ring* is a commutative ring with $1$ isomorphic to $\mathbb{Z}[x_1, \dots, x_n] / I$ for some $n \ge 0$ and some ideal $I$; its elements, and hence polynomials over it, can be encoded by finite data. An *order* is an integral domain whose additive group is isomorphic to $\mathbb{Z}^n$ for some $n \ge 1$, and a *maximal order* is one not properly contained with finite index in another order; the maximal orders are exactly the rings of integers $\mathcal{O}_K$ of number fields $K$.

**Theorem (Koymans–Pagano).**

1. Let $R$ be a maximal order, that is, $R = \mathcal{O}_K$ for a number field $K$. Then $\mathbb{Z}$ is a Diophantine subset of $R$: there is a polynomial $P(t, y_1, \dots, y_m)$ with coefficients in $R$ such that $t \in R$ lies in $\mathbb{Z}$ if and only if $P(t, y) = 0$ for some $y \in R^m$. In particular, Hilbert's tenth problem over $R$ is undecidable.
2. Let $R$ be a finitely generated ring of infinite cardinality. Then Hilbert's tenth problem over $R$ is undecidable: there is no algorithm that decides, for a polynomial with coefficients in $R$, whether it has a zero in $R^n$.

Conventions: for a finite ring the problem is decidable by trying all points. Clause 2 follows from clause 1 by Eisenträger's reduction, which shows that it suffices to prove that $\mathbb{Z}$ is Diophantine over every maximal order. Clause 1 had previously been known for totally real maximal orders (Denef) and other families, and for all maximal orders conditionally on the Birch and Swinnerton-Dyer conjecture (Mazur–Rubin). Two other groups (Alpöge, Bhargava, Ho and Shnidman, and Zywina) proved the same result independently.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Integral closure of ℤ in a field and the ring of integers of a number field](../../algebraic-number-theory/number-fields-embeddings/ring-of-integers.md)
- [Diophantine subsets of a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/is-diophantine-set.md)
- [Commutative ring with identity](../../../Algebra/rings-and-fields/commutative-ring-with-identity.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Hilbert's tenth problem over a ring of integers is undecidable given a rank-one elliptic curve](h10-undecidable-given-a-rank-one-elliptic-curve.md)
- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

By Poonen's criterion, it suffices to find, for the number field $K$, an elliptic curve $E$ over $\mathbb{Q}$ with $\operatorname{rk} E(\mathbb{Q}) = \operatorname{rk} E(K) = 1$; more precisely the proof needs a curve with a point of infinite order built in and with $2$-Selmer rank one over $K$. Koymans and Pagano work with a family of curves whose defining cubic splits as $(x - a_1 f(m/n))(x - a_2 f(m/n))(x - a_3 f(m/n))$ for fixed $a_1, a_2, a_3 \in R$, so that a rational point is present from the outset. The $2$-Selmer ranks in such a family are governed by the primes dividing $n(m - a_1 n)(m - a_2 n)(m - a_3 n)$, a product of four linear forms. Using the Green–Tao theorem on linear forms in primes, extended to maximal orders by Kai, all four forms can be made prime at once, and a descent argument then forces the Selmer rank, and with it the Mordell–Weil rank, to equal one over both $\mathbb{Q}$ and $K$. The undecidability over $\mathbb{Z}$ transfers to $R$ through the Diophantine definition of $\mathbb{Z}$. A good expansion links pages for Eisenträger's reduction to maximal orders, for the Green–Tao theorem on linear forms in primes and its extension to maximal orders by Kai, and for the $2$-Selmer descent that controls the ranks.

## Sources

- Peter Koymans and Carlo Pagano, *Hilbert's tenth problem for finitely generated rings*, Notices Amer. Math. Soc. 73 (2026), no. 6, https://doi.org/10.1090/noti3339, read in the copy arXiv:2602.04468v1: clause 2 is Theorem 1.1 and clause 1 is Theorem 6.1 there, both presented as established results; Eisenträger's reduction and the definitions of finitely generated rings and orders are in its Section 4.
- Peter Koymans and Carlo Pagano, *Hilbert's tenth problem via additive combinatorics*, J. Amer. Math. Soc. 40 (2026), no. 1, 195–234, https://doi.org/10.1090/jams/1081, the original proof, cited for attribution; the statement rests on the survey above, whose copy was read.
