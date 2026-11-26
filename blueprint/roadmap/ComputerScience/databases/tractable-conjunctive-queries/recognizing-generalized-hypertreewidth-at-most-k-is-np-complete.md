# Recognizing generalized hypertreewidth at most k is NP-complete

Fix $k > 1$. Deciding whether a given conjunctive query has generalized hypertreewidth at most $k$ is NP-complete.
Consequently, unless P = NP, no polynomial-time algorithm computes, for every input query in $\mathrm{GHW}(k)$, a
generalized hypertree decomposition of width $k$. For $k = 1$ (acyclic queries) a join tree is computable in linear
time.

## Expansion

This node states a precise result. The cited source proves Theorem 22.9 from Proposition 22.10 but does not prove
Proposition 22.10; a good expansion adds the source of the NP-hardness proof for every fixed $k > 1$, after checking
it, under `## Sources`.

## Depends on

- [Generalized hypertree decompositions and generalized hypertreewidth](generalized-hypertree-decompositions-and-width.md)
- [NP-complete decision problems](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Theorem 22.9 and Proposition 22.10 (p. 188), and Proposition 18.8 (p. 157).
