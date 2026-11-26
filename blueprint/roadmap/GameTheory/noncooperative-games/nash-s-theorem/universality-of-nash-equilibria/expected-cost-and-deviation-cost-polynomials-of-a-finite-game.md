# Expected-cost and deviation-cost polynomials of a finite game

Let $G$ be a finite game with strategy sets $S_i$ and costs $c_i$. Introduce one real variable $x_{i,a}$ for each player $i$ and each $a \in S_i$. The *expected-cost polynomial* of player $i$ is

$$
E_i(x) = \sum_{s \in \prod_j S_j} c_i(s) \prod_{j} x_{j, s_j},
$$

and the *deviation-cost polynomial* of a pure strategy $a \in S_i$ is $D_{i,a}(x) = \sum_{s : s_i = a} c_i(s) \prod_{j \ne i} x_{j, s_j}$. Each $E_i$ is affine in every block $(x_{j,b})_{b \in S_j}$, and $D_{i,a}$ does not involve player $i$'s own block. On profiles whose blocks are probability vectors, $E_i$ is the expected cost and $D_{i,a}$ the expected cost of deviating to $a$.

## Depends on

- [Mixed Nash equilibrium](../is-mixed-nash.md)
- [Expected payoff of a mixed profile](../expected-payoff.md)

## Sources

- Ruchira S. Datta, "Universality of Nash Equilibria", Mathematics of Operations Research, 2003.
