# Optimal mixed strategy to commit to (two-player normal form)

In a bimatrix game with rational payoffs, let the leader commit to a mixed strategy and the follower best respond, with ties broken in the
leader's favour (optimistic tie-breaking). For each follower pure strategy $j$, solve the linear program that maximizes the leader's expected
utility over leader mixed strategies under which $j$ is a follower best response (a closed region defined by linear inequalities); an optimal
commitment is an optimal solution of the best feasible program. Hence an optimal commitment exists and is computable in time polynomial
in the explicit size. With pessimistic tie-breaking the optimum need not be attained. NP-hardness for Bayesian or three-player games is
cited context, not part of the statement.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Proof prerequisite: linear programs with rational data are solvable in time polynomial in their bit size (ellipsoid or interior-point methods).

## Depends on

- [Expected payoff of a mixed profile](nash-s-theorem/expected-payoff.md)
- [Explicit encoding and size of finite games](explicit-encoding-and-size-of-finite-games.md)
- [Linear program](../../Geometry/convex-geometry/linear-programming/linear-program.md)

## Sources

- Learning and Approximating the Optimal Strategy to Commit To — Letchford, Conitzer, Munagala, SAGT 2009, Section 1 (tie-breaking in the leader's favour; attainment) and Section 2.2 (the linear programs, after Conitzer and Sandholm 2006). <https://users.cs.duke.edu/~conitzer/learningSAGT09.pdf>
