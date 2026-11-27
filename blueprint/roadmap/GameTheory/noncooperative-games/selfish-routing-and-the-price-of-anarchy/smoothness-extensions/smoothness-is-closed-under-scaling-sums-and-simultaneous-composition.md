# Smoothness is closed under scaling, sums and simultaneous composition

Consider cost games with nonnegative costs on a fixed finite set of players who share a common strategy set, and let $\lambda \ge 0$ and $\mu$ be reals. If a game with costs $c_i$ is $(\lambda, \mu)$-smooth, then so is the game with costs $\alpha c_i$ for every $\alpha \ge 0$. If $G_A$ is $(\lambda_A, \mu_A)$-smooth and $G_B$ is $(\lambda_B, \mu_B)$-smooth, their simultaneous composition, in which each player chooses a pair of strategies, one in each game, and pays the sum of its two costs, is $(\max(\lambda_A, \lambda_B), \max(\mu_A, \mu_B))$-smooth. Restricting every player to the strategies satisfying a fixed predicate preserves $(\lambda, \mu)$-smoothness; restricting the composition of two $(\lambda, \mu)$-smooth games on the same strategy set to the diagonal pairs $(a, a)$ shows that the game with costs $c_i + c'_i$ is $(\lambda, \mu)$-smooth. A $(\lambda, \mu)$-smooth game is $(\lambda', \mu')$-smooth for all $\lambda' \ge \lambda$ and $\mu' \ge \mu$.

## Proof sketch

The smoothness inequality is linear in the cost functions and additive over independent components; enlarging $\lambda$ and $\mu$ only enlarges its right-hand side because costs are nonnegative, so both composed games satisfy it with the larger constants, and restricting the strategies only removes instances of the inequality.

## Depends on

- [Smooth game](../../no-regret-dynamics/is-smooth.md)

## Sources

- Tim Roughgarden, "Intrinsic Robustness of the Price of Anarchy", Journal of the ACM 62(5), 2015, Definition 2.1.
- Samuel Merten, Alexander Bagnall and Gordon Stewart, "Verified Learning Without Regret: From Algorithmic Game Theory to Distributed Systems with Mechanized Complexity Guarantees", Programming Languages and Systems (ESOP 2018), LNCS 10801, 2018, 561–588, Section 4, Definition 1 and Fig. 4 (the rules ScalarSmooth, ProductSmooth and SigmaSmooth, and the derived combinator built as a restriction of a product to equal components), and the text after Fig. 4 (smoothness still holds when $\lambda$ and $\mu$ are replaced by larger values).
