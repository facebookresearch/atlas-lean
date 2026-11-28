# Uncountably many totally real fields have undecidable Hilbert's tenth problem over their integers

For every prime $p$ there are uncountably many pairwise non-isomorphic totally real fields $L$ of algebraic numbers inside $\mathbb{Q}_p$ such that $\mathbb{Z}$ is Diophantine over the ring of integers of $L$, so Hilbert's tenth problem over it is undecidable, and $\mathbb{Z}$ is first-order definable in $L$, so the theory of $L$ is undecidable.

Fix a prime $p$. There are uncountably many pairwise non-isomorphic fields $L$ with the following properties: $L$ is a totally real field of algebraic numbers (every element of $L$ is algebraic over $\mathbb{Q}$ and every embedding of $L$ into $\mathbb{C}$ has image in $\mathbb{R}$), $L$ embeds in the field $\mathbb{Q}_p$ of $p$-adic numbers, and both of the following hold.

1. There is a Diophantine definition of $\mathbb{Z}$ in the ring of integers $\mathcal{O}_L$ of $L$. In particular Hilbert's tenth problem has a negative answer for $\mathcal{O}_L$: there is no algorithm that decides whether a polynomial in several variables with coefficients in $\mathcal{O}_L$ has a zero in $\mathcal{O}_L$, where the coefficients are given as algebraic numbers promised to lie in $\mathcal{O}_L$, as for rings of algebraic numbers in the linked definition.
2. There is a first-order definition of the ring $\mathbb{Z}$ in the field $L$, in the language of rings. In particular the first-order theory of $L$ is undecidable.

Conventions: there are only countably many number fields up to isomorphism, so all but countably many of these fields have infinite degree over $\mathbb{Q}$, and $\mathcal{O}_L$ is the integral closure of $\mathbb{Z}$ in $L$. Clause 1 concerns deciding solvability on valid inputs; it does not assert that membership in $\mathcal{O}_L$ is decidable, and it cannot rest on a computable presentation of every $\mathcal{O}_L$: only countably many rings have one, while the rings $\mathcal{O}_L$ here are pairwise non-isomorphic, since each $L$ is the fraction field of $\mathcal{O}_L$.

## Depends on

- [Hilbert's tenth problem over a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/hilbert-s-tenth-problem-over-a-ring.md)
- [Integral closure of ℤ in a field and the ring of integers of a number field](../../algebraic-number-theory/number-fields-embeddings/ring-of-integers.md)
- [Diophantine subsets of a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/is-diophantine-set.md)
- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)
- [The field of p-adic numbers](../../p-adic-numbers/p-adic-numbers.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [The halting problem is recognizable by multi-stack machines](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/tm2-recognizable-halting.md)
- [The halting problem is undecidable by multi-stack machines](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halting.md)
- [The first-order theory of the ring of integers is undecidable](../../../Logic/proof-theory/g-del-s-incompleteness-theorems/first-order-theory-of-the-integers-is-undecidable.md)

## Expansion

The fields come from Diophantine stability. A variety $V$ over a number field $K$ is Diophantine stable in an extension $L/K$ when $V(L) = V(K)$. Mazur and Rubin prove that an irreducible curve over $K$ whose normalization has genus at least $1$ and whose jacobian has all its geometric endomorphisms defined over $K$ is, for every prime $\ell$ in a set of primes of positive density, Diophantine stable in infinitely many cyclic extensions of degree $\ell^n$ completely split at any given finite set of places (Theorem 1.3 of arXiv:1503.04642v3). Applying this repeatedly along a tower of cyclic extensions of increasing prime-power degrees gives uncountably many pairwise non-isomorphic extensions $L$ of $K$ in which the places of a given finite set $\Sigma$ split completely and $V(L) = V(K)$ (Theorem 4.1 there). With $K = \mathbb{Q}$, a non-CM elliptic curve $E$ over $\mathbb{Q}$ of positive rank and $\Sigma = \{\infty, p\}$, this gives uncountably many totally real $L$ in which $p$ splits completely, so that $L$ embeds in $\mathbb{Q}_p$, and $E(L) = E(\mathbb{Q})$ is finitely generated and infinite (Corollary 4.2 there). Two theorems of Shlapentokh finish the proof: for a totally real field $L$ with such an elliptic curve, $\mathbb{Z}$ has a Diophantine definition over $\mathcal{O}_L$ (her Main Theorem A in Arch. Math. Logic 48), which gives clause 1; and since $p$ splits completely in $L$, all its local degrees are $1$, so $p$ is completely $q$-bounded for every prime $q$, which is the hypothesis of her Theorem 8.5 (Theorem 8.5 of arXiv:1307.0743v3) and gives a first-order definition of $\mathbb{Z}$ in $L$, which is clause 2. In clause 1 the negative answer follows by the Davis–Putnam–Robinson–Matiyasevich theorem applied to a listable undecidable set such as the halting set: for $f \in \mathbb{Z}[x_1, \dots, x_n]$, the system $f(x) = 0$, $g(x_i, y^{(i)}) = 0$ formed with the Diophantine definition $g$ of $\mathbb{Z}$ is equivalent over $\mathcal{O}_L$ to the single equation stating that the sum of the squares of its members vanishes, because $L$ is totally real and so embeds in $\mathbb{R}$; this equation has algebraic coefficients in $\mathcal{O}_L$ taken from the finitely many coefficients of $g$, so a solver on valid inputs would solve Hilbert's original problem, and in clause 2 relativizing quantifiers to the definition of $\mathbb{Z}$ transfers the undecidability of the theory of $(\mathbb{Z}, +, \cdot, 0, 1)$ to $L$.

A good expansion adds and links pages for Corollary 4.2 of arXiv:1503.04642v3 and for Shlapentokh's two theorems.

## Sources

- Barry Mazur and Karl Rubin, with an appendix by Michael Larsen, *Diophantine stability*, Amer. J. Math. 140 (2018), no. 3, 517–616, https://doi.org/10.1353/ajm.2018.0014; the statement is Corollary 1.6 of arXiv:1503.04642v3, the version read, proved in Section 4 from Theorem 1.3, Theorem 4.1 and Corollary 4.2.
- Alexandra Shlapentokh, *Rings of algebraic numbers in infinite extensions of $\mathbb{Q}$ and elliptic curves retaining their rank*, Arch. Math. Logic 48 (2009), no. 1, 77–114, https://doi.org/10.1007/s00153-008-0118-y; Main Theorem A, as applied in Section 4 of arXiv:1503.04642v3.
- Alexandra Shlapentokh, *First-order decidability and definability of integers in infinite algebraic extensions of the rational numbers*, Israel J. Math. 226 (2018), no. 2, 579–633, https://doi.org/10.1007/s11856-018-1708-y; Theorem 8.5 of arXiv:1307.0743v3, the version read, as applied in Section 4 of arXiv:1503.04642v3.
