# Mixed Nash equilibria of polymatrix games via pairwise forms

For independent mixed strategies $p$ in a polymatrix game, the expected cost of player $i$ is $\sum_{j \ne i} p_i^\top C_{ij} p_j$ and the expected cost of the pure strategy $a$ is $\sum_{j \ne i} (C_{ij} p_j)(a)$. Hence $p$ is a mixed Nash equilibrium if and only if for every player $i$ and every $a \in S_i$, $\sum_{j \ne i} p_i^\top C_{ij} p_j \le \sum_{j \ne i} (C_{ij} p_j)(a)$; these are bilinear conditions in the pairwise strategies.

## Proof sketch

Expectation of a sum of pairwise terms under a product distribution factors into bilinear forms; then apply the pure-deviation criterion.

## Depends on

- [Polymatrix game](polymatrix-game.md)
- [Mixed Nash equilibrium](../is-mixed-nash.md)

## Proof depends on

- [Pure deviations suffice to check a mixed Nash equilibrium](../pure-deviations-suffice-for-mixed-nash-equilibrium.md)

## Sources

- Elena B. Janovskaja, "Equilibrium Points in Polymatrix Games", Litovskii Matematicheskii Sbornik, 1968.
- Joseph T. Howson Jr., "Equilibria of Polymatrix Games", Management Science, 1972.
