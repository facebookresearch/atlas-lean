# Data exchange: universal solutions and certain answers of UCQs

Fix a data-exchange setting: source and target schemas, source-to-target tuple-generating
dependencies, and target dependencies consisting of weakly acyclic tuple-generating dependencies and
equality-generating dependencies, none of which contains a constant (as in the cited source: with $S(x) \to T(c)$, $I = \{S(a)\}$
and $q(z) = T(z)$ the null-free tuple $(c)$ of $q(J)$ is not over the active domain of $I$). Fix a union of conjunctive queries $q$ over the target. A solution for a source instance $I$ is a target
instance $J$ such that $I$ and $J$ together satisfy all the dependencies, and the certain answers of $q$ on
$I$ are the tuples over the active domain of $I$ that belong to $q(J)$ for every solution $J$ (so when $I$ has no
solution they are all tuples over that active domain, not arbitrary constants). For every source
instance $I$, the chase of $I$ either fails, in which case $I$ has no solution, or terminates in a number
of steps polynomial in $\lvert I \rvert$ with a canonical universal solution $J$; in the latter case the
certain answers of $q$ on $I$ are the null-free tuples of $q(J)$. Hence, for the fixed setting and query,
deciding solution existence and computing certain answers take time polynomial in $\lvert I \rvert$ (data
complexity); this is not a combined-complexity bound.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Weakly acyclic dependencies have polynomially bounded chase](weakly-acyclic-dependencies-have-polynomially-bounded-chase.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Containment of unions of conjunctive queries](../conjunctive-queries/cores-and-minimization/containment-of-unions-of-conjunctive-queries.md)

## Proof depends on

- [Weakly acyclic dependencies have polynomially bounded chase](weakly-acyclic-dependencies-have-polynomially-bounded-chase.md)
- [Successful terminating chases yield universal models](successful-terminating-chases-yield-universal-models.md)

## Sources

- Data Exchange: Semantics and Query Answering (Fagin, Kolaitis, Miller, Popa), TCS 2005, course copy — Theoretical Computer Science 336 (2005), Definitions 2.1 and 4.1, Theorem 3.3, Theorem 3.9, Corollary 3.10, Proposition 4.2 and Corollary 4.3, and p. 97 (no constants in the dependencies). <https://www.cis.upenn.edu/~val/CIS650/DataX-tcs.pdf>
