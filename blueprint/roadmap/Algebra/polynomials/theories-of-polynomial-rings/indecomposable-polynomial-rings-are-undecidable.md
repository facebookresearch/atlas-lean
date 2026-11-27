# Polynomial rings over indecomposable rings have undecidable theories

If a commutative ring R has no idempotents other than 0 and 1, then every polynomial ring over R, in any nonempty set of variables, has an undecidable first-order theory in the language of rings, and arithmetic is interpretable in it.

Let $R$ be a commutative ring with identity that is *indecomposable*: its only idempotents are $0$ and $1$. Let $X$ be a nonempty set of indeterminates and $S = R[X]$ the polynomial ring, viewed as a structure for the language $(0, 1, +, \cdot)$ of rings. $R[X]$ is indecomposable exactly when $R$ is.

**Theorem (Barone–Caro-Montoya–Naziazeno).** For every indecomposable commutative ring $R$ with identity and every nonempty set $X$ of indeterminates:

1. the theory $\operatorname{Th}(R[X])$ of $R[X]$ in the language of rings is undecidable, by a proof that is uniform over the class of all such rings;
2. arithmetic is interpretable in $R[X]$.

Conventions: $R$ need not be reduced; no parameters are allowed in sentences. The reduced case in one variable is the linked theorem.

## Depends on

- [Commutative ring with identity](../../rings-and-fields/commutative-ring-with-identity.md)
- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)
- [Predicates decidable by a single-tape Turing machine](../../../TheoryOfComputation/turing-machines/single-tape/decidable-and-recognizable-predicates-on-single/single-tape-decidable.md)

## Proof depends on

- [Polynomial rings over reduced indecomposable rings have undecidable theories](reduced-indecomposable-polynomial-rings-are-undecidable.md)

## Expansion

The nilradical $N_S$ of $S = R[X]$, its set of nilpotent elements, is defined by one formula in every polynomial ring, and if $S$ is indecomposable then $S/N_S$ is a reduced indecomposable polynomial ring. A definable ideal gives a uniform interpretation of $S/N_S$ in $S$, and composing it with the uniform translation of sentences about $(\mathbb{Z}^+, +, \mid)$ into sentences about reduced indecomposable polynomial rings, from the linked theorem, yields undecidability for all indecomposable polynomial rings at once. As in the source, a polynomial ring in several variables is written as a univariate polynomial ring over the polynomial ring in the other variables. For clause 2, the source builds two-dimensional interpretations of arithmetic in univariate polynomial rings over fields (one for positive characteristic, one for fields with an element of infinite multiplicative order) and transfers them through the same factor-ring argument.

A good expansion adds and links pages for the uniform first-order definition of the nilradical in polynomial rings and for the interpretations of arithmetic in polynomial rings over fields.

## Sources

- Marco Barone, Nicolás Caro-Montoya and Eudes Naziazeno, *Undecidability of indecomposable polynomial rings*, Archive for Mathematical Logic 64 (2025), no. 1–2, 185–203 (published online 2024), https://doi.org/10.1007/s00153-024-00936-3; read as arXiv:2304.02165v2, where both clauses are the conclusion of Section 3.3 (from Theorems 3.2 and 3.3, Lemma 3.4 and Proposition 3.5), and the indecomposability criterion is recalled in Section 1.1.
