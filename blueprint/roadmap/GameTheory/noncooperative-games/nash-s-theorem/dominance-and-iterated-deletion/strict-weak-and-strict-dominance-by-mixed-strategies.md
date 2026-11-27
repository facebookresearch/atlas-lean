# Strict, weak and ε-strict dominance by mixed strategies

In a finite cost-minimization game, a pure strategy $a \in S_i$ is *strictly dominated* by a mixed strategy $q$ of player $i$ if $\sum_b q(b)\, c_i(b, s_{-i}) < c_i(a, s_{-i})$ for every profile $s_{-i}$ of the others; it is *$\varepsilon$-strictly dominated* if $\sum_b q(b) c_i(b, s_{-i}) + \varepsilon \le c_i(a, s_{-i})$ for all $s_{-i}$; and it is *weakly dominated* if the inequality is non-strict for all $s_{-i}$ and strict for at least one. Domination by a pure strategy is the case $q = e_b$. Domination may also be taken relative to a product of subsets $R = \prod_j R_j$ of strategies, quantifying only over $s_{-i} \in R_{-i}$.

## Depends on

- [Strategic Game](../../../not-yet-classified/part-02/strategic-game/strategic-game.md)
- [Strictly dominant strategy](../../../not-yet-classified/part-01/dominant-strategy/is-strictly-dominant.md)

## Sources

- Eva Tardos and Vijay V. Vazirani, "Basic Solution Concepts and Computational Issues", Algorithmic Game Theory, Cambridge University Press, 2007.
- Noam Nisan, Tim Roughgarden, Eva Tardos and Vijay V. Vazirani, "Algorithmic Game Theory", Cambridge University Press, 2007.
