# Exact potentials of polymatrix games

A polymatrix game admits an exact potential if and only if it is pairwise potential: for every pair $i \ne j$ there are functions $u_{ij}$ on $S_i$ and $v_{ij}$ on $S_j$ with $C_{ij}(a, b) - C_{ji}(b, a) = u_{ij}(a) - v_{ij}(b)$ (the skew part is separable). In particular every symmetric polymatrix game has the exact potential $\Phi(s) = \sum_{\{i, j\}} C_{ij}(s_i, s_j)$, its social cost equals $2\Phi$, it has the finite improvement property, and some pure Nash equilibrium minimizes social cost, so its price of stability is $1$.

## Proof sketch

Evaluate the four-cycle condition of the Monderer–Shapley characterization on a pair of players: only the $(i, j)$ and $(j, i)$ matrices contribute, and the vanishing condition is exactly separability of the skew part. For symmetric games the edge potential changes by exactly the deviator's cost change.

## Depends on

- [Polymatrix game](polymatrix-game.md)
- [Exact potential](../../potential-games/is-exact-potential.md)

## Proof depends on

- [Monderer–Shapley cycle characterization of exact potential games](../../potential-games/potential-game-characterizations/monderer-shapley-cycle-characterization-of-exact-potential-games.md)
- [Generalized ordinal potentials give the finite improvement property](../../potential-games/potential-game-characterizations/generalized-ordinal-potentials-give-the-finite-improvement-property.md)

## Sources

- Elena B. Janovskaja, "Equilibrium Points in Polymatrix Games", Litovskii Matematicheskii Sbornik, 1968.
- Joseph T. Howson Jr., "Equilibria of Polymatrix Games", Management Science, 1972.
- Dov Monderer and Lloyd S. Shapley, "Potential Games", Games and Economic Behavior, 1996.
