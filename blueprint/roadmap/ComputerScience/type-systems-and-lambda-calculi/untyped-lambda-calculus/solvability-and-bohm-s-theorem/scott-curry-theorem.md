# The Scott–Curry theorem

Fix a recursive enumeration $n \mapsto t_n$ of the untyped λ-terms up to α-equivalence, so that a set of terms is *recursive* when the corresponding set of
indices is. Let $X$ and $Y$ be two non-empty disjoint sets of terms, each closed under β-conversion: if $t \in X$ and $t \simeq_\beta t'$ then $t' \in X$, and likewise for $Y$.
Then $X$ and $Y$ are recursively inseparable: no recursive set $A$ satisfies $X \subseteq A$ and $Y \cap A = \emptyset$.

**Corollaries.**

- No non-empty proper subset of the terms that is closed under β-conversion is recursive.
- β-convertibility is undecidable; in particular the set of terms β-convertible to $\lambda x y.\, x$ is not recursive (Church).
- The set of β-normalizable terms and the set of solvable terms are not recursive.

## Depends on

- [Beta equivalence in the untyped term model](../../system-f/the-existing-untyped-beta-conversion-term-model/beta-eq.md)
- [Head normal forms and solvable terms](head-normal-forms-and-solvable-terms.md)

## Proof depends on

- [The second fixed point theorem](second-fixed-point-theorem.md)
- [λ-definable functions are exactly the partial recursive functions](../../../../TheoryOfComputation/equivalence-of-models/counter-and-combinator-models/lambda-definable-functions-are-exactly-the.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 2, Theorem 2.20 and Corollary 2.21, with the remark that follows it.
- M. H. B. Sørensen and P. Urzyczyn, *Lectures on the Curry–Howard Isomorphism*, lecture notes, University of Copenhagen, May 1998: Theorem 1.5.23 (Curry, Scott) and Corollaries 1.5.25–1.5.26 (Church).
