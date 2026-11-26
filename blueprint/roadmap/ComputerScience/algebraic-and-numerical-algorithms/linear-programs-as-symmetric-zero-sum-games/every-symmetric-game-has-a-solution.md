# Every symmetric zero-sum game has a solution

Let $K$ be a linearly ordered field, $N$ a nonempty finite index set and $P \in K^{N \times N}$ skew-symmetric. Then there is $z \in K^N$ with $z \ge 0$, $\sum_k z_k = 1$ and $Pz \ge 0$.

## Proof sketch

By the minimax theorem over $K$ the game has a value $v$ with optimal strategies. Skew-symmetry gives $p^{\mathsf T} P p = 0$ for every $p$, so playing an optimal strategy against itself forces $v = 0$. An optimal strategy of the player guaranteeing at least $0$ is then a solution.

## Depends on

- [Symmetric zero-sum game and its solutions](symmetric-zero-sum-game.md)

## Proof depends on

- [Von Neumann's minimax theorem over every linearly ordered field](minimax-theorem-over-ordered-fields.md)

## Sources

- Ilan Adler, "The equivalence of linear programs and zero-sum games", International Journal of Game Theory 42(1), 165-177, 2013.
