# Correctness of support enumeration for bimatrix games

For a bimatrix game with $m$ and $n$ pure strategies, consider the algorithm that enumerates pairs of supports
$(I, J)$ and, for each, solves the linear feasibility system expressing that mixed strategies supported on $I$
and $J$ are best responses to each other. Every feasible solution found is a Nash equilibrium, and since a Nash
equilibrium exists, some support pair is feasible; hence the algorithm always outputs an equilibrium. There are at most $2^{m+n}$ support pairs, and each test is a linear feasibility problem of size polynomial in the game.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Proof prerequisite: Best-response (support) condition.
- Statement prerequisite: Explicit encoding and size of finite games.

## Proof depends on

- [Nash's theorem](../nash-s-theorem/exists-is-mixed-nash.md)

## Sources

- R. Savani and B. von Stengel, *Hard-to-solve bimatrix games*, Econometrica 74 (2006) 397–429, Lemma 1 and §2. <http://www.maths.lse.ac.uk/Personal/stengel/TEXTE/savanistengel.pdf>
