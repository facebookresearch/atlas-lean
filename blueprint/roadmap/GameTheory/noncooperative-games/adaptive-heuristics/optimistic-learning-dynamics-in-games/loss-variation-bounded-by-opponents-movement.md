# A player's loss variation is bounded by the other players' movement

In a finite normal-form game with losses in $[0, 1]$, let player $i$'s expected loss vector against mixed strategies $x_{-i}$ be $\ell_i(x_{-i}) \in [0, 1]^{n_i}$. For any two profiles $x_{-i}, y_{-i}$ of the other players,

$$
\lVert \ell_i(x_{-i}) - \ell_i(y_{-i}) \rVert_\infty \le \sum_{j \ne i} \lVert x_j - y_j \rVert_1 .
$$

Consequently, in repeated play, $\sum_t \lVert \ell_i^t - \ell_i^{t-1}\rVert_\infty^2 \le (m - 1) \sum_{j \ne i} \sum_t \lVert x_j^t - x_j^{t-1}\rVert_1^2$.

## Proof sketch

The map $x_{-i} \mapsto \ell_i(x_{-i})(a)$ is multilinear in the opponents' strategies with coefficients in $[0, 1]$. Change one opponent's strategy at a time (a hybrid argument): changing $x_j$ to $y_j$ with the others fixed alters each coordinate by at most $\tfrac12 \lVert x_j - y_j\rVert_1 \le \lVert x_j - y_j \rVert_1$, since it is an expectation of a $[0,1]$-valued function under two distributions. Summing over $j$ gives the first claim, and Cauchy–Schwarz gives the second.

## Depends on

- [Optimistic Hedge in a repeated normal-form game](optimistic-hedge-in-games.md)
- [Expected payoff of a mixed profile](../../nash-s-theorem/expected-payoff.md)

## Sources

- V. Syrgkanis, A. Agarwal, H. Luo, R. E. Schapire, "Fast Convergence of Regularized Learning in Games", NeurIPS 2015, arXiv:1507.00407.
