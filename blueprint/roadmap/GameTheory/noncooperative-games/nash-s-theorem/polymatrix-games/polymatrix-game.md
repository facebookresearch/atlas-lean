# Polymatrix game

A *polymatrix game* has players $I$ with finite strategy sets $S_i$ and, for each ordered pair of distinct players $(i, j)$, a cost matrix $C_{ij} : S_i \times S_j \to \mathbb{R}$. Player $i$'s cost at profile $s$ is $\sum_{j \ne i} C_{ij}(s_i, s_j)$. A bimatrix game is the two-player case. The polymatrix game is *symmetric* if $C_{ij}(a, b) = C_{ji}(b, a)$ for all $i \ne j$, $a$, $b$.

## Depends on

- [Strategic Game](../../../not-yet-classified/part-02/strategic-game/strategic-game.md)
- [Nash equilibrium of a bimatrix game](../../bimatrix-games-and-the-lemke-howson-algorithm/is-bimatrix-nash.md)

## Sources

- Elena B. Janovskaja, "Equilibrium Points in Polymatrix Games", Litovskii Matematicheskii Sbornik, 1968.
- Joseph T. Howson Jr., "Equilibria of Polymatrix Games", Management Science, 1972.
