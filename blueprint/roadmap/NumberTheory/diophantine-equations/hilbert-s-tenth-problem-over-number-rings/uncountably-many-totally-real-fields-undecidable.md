# Uncountably many totally real fields have undecidable Hilbert's tenth problem over their integers

For every prime $\ell$ there are uncountably many pairwise non-isomorphic totally real fields $L$ of algebraic numbers inside $\mathbb{Q}_\ell$ such that $\mathbb{Z}$ is Diophantine over the ring of integers of $L$, so Hilbert's tenth problem over it is undecidable, and $\mathbb{Z}$ is first-order definable in $L$, so the theory of $L$ is undecidable.

Fix a prime $\ell$. There are uncountably many pairwise non-isomorphic fields $L$ with the following properties: $L$ is a totally real field of algebraic numbers (every element of $L$ is algebraic over $\mathbb{Q}$ and every embedding of $L$ into $\mathbb{C}$ has image in $\mathbb{R}$), $L$ embeds in the field $\mathbb{Q}_\ell$ of $\ell$-adic numbers, and both of the following hold.

1. There is a Diophantine definition of $\mathbb{Z}$ in the ring of integers $\mathcal{O}_L$ of $L$. In particular Hilbert's tenth problem has a negative answer for $\mathcal{O}_L$: there is no algorithm that decides whether a polynomial in several variables with coefficients in $\mathcal{O}_L$ has a zero in $\mathcal{O}_L$.
2. There is a first-order definition of the ring $\mathbb{Z}$ in the field $L$, in the language of rings. In particular the first-order theory of $L$ is undecidable.

Conventions: there are only countably many number fields up to isomorphism, so all but countably many of these fields have infinite degree over $\mathbb{Q}$, and $\mathcal{O}_L$ is the integral closure of $\mathbb{Z}$ in $L$.

## Depends on

- [Hilbert's tenth problem over a ring](hilbert-s-tenth-problem-over-a-ring.md)
- [Integral closure of ℤ in a field and the ring of integers of a number field](../../algebraic-number-theory/number-fields-embeddings/ring-of-integers.md)
- [Diophantine subsets of a ring](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/is-diophantine-set.md)
- [Complete theory of a first-order structure](../../../Logic/first-order-logic/theory-of-structure.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The result is a consequence of Diophantine stability. A variety $V$ over a number field $K$ is Diophantine stable in an extension $L/K$ when $V(L) = V(K)$, and $\ell$-Diophantine stable over $K$ when, for every $n \ge 1$ and every finite set $\Sigma$ of primes of $K$, there are infinitely many cyclic extensions $L/K$ of degree $\ell^n$ in which every prime of $\Sigma$ splits completely and $V(L) = V(K)$. Mazur and Rubin prove that a simple abelian variety over $K$ with all geometric endomorphisms defined over $K$ is $\ell$-Diophantine stable for every $\ell$ in a set of primes of positive density (their Theorem 1.2, as quoted by Ray and Weston), and they obtain the statement above by specializing this to elliptic curves. In clause 1 the negative answer follows from the Diophantine definition of $\mathbb{Z}$ by the Davis–Putnam–Robinson–Matiyasevich theorem: a polynomial with integer coefficients has a zero in $\mathbb{Z}$ exactly when the system formed by it and the defining equations of $\mathbb{Z}$ for each unknown has a zero in $\mathcal{O}_L$. In clause 2, relativizing quantifiers to the definition of $\mathbb{Z}$ translates sentences about $(\mathbb{Z}, +, \cdot)$, whose theory is undecidable, into sentences about $L$.

## Sources

- Barry Mazur and Karl Rubin, with an appendix by Michael Larsen, *Diophantine stability*, Amer. J. Math. 140 (2018), no. 3, 517–616, https://doi.org/10.1353/ajm.2018.0014. Ray and Weston quote the result as Corollary 1.6 of this paper; it is read in the version of their paper below (Corollary 1.2 of arXiv:2304.09742v3), as is Theorem 1.2 of this paper (Theorem 1.1 there).
- Anwesh Ray and Tom Weston, *Diophantine stability for elliptic curves on average*, European J. Math. 11 (2025), no. 4, article 78, https://doi.org/10.1007/s40879-025-00872-3; the statement is recalled verbatim as Corollary 1.2 of arXiv:2304.09742v3.
