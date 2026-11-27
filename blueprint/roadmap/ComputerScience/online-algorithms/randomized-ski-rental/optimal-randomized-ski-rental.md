# Optimal randomized competitive ratio of discrete ski rental

For integer purchase price $B \ge 1$, let

$$
\rho_B = \frac{1}{1 - (1 - 1/B)^B} = \frac{B^B}{B^B - (B-1)^B}.
$$

The randomized strategy that rents for $t \in \{0, \dots, B-1\}$ days and buys on day $t + 1$, choosing $t$ with probability proportional to $(B - 1)^{B-1-t} B^t$, has expected cost exactly $\rho_B \cdot \min(n, B)$ on a season of $n$ days, so it is $(\rho_B, 0)$-competitive against an oblivious adversary. Conversely no randomized strategy is $(c, 0)$-competitive for $c < \rho_B$. Moreover $\rho_B \le e/(e-1)$, $\rho_B \to e/(e - 1)$ as $B \to \infty$, $\rho_2 = 4/3$, $\rho_3 = 27/19$, and $\rho_B < 2 - 1/B$ for all $B \ge 2$.

## Proof sketch

The buying probabilities equalize the ratio: for each season length $n \le B$ the expected cost is a geometric sum equal to $\rho_B n$, and longer seasons cost the same as $n = B$. For the lower bound apply Yao averaging to the adversary that ends the season after $k + 1$ days with weight $(B-1)^k B^{B-2-k}$ for $k < B - 1$, and after $2B - 1$ days with weight $(B - 1)^{B-1}$; every deterministic rent-then-buy strategy then has mean cost at least $\rho_B$ times the mean optimum. To meet the finiteness hypothesis of Yao averaging, restrict the problem to the $B$ season lengths $1, \dots, B - 1$ and $2B - 1$ in the adversary's support: on them a deterministic strategy is determined by its behaviour up to day $2B - 1$, which is to buy on one of the days $1, \dots, 2B - 1$ or not at all, so there are finitely many deterministic strategies, and every randomized strategy induces a distribution over them with the same expected costs on these seasons. Yao averaging then gives, for every randomized strategy, a season in the support whose expected cost is at least $\rho_B$ times its optimum, which is positive. The limit follows from $(1 - 1/B)^B \to e^{-1}$ and $(1 - 1/B)^B \le e^{-1}$.

## Depends on

- [Randomized online strategies against an oblivious adversary](../competitive-analysis/randomized-online-strategies.md)
- [Deterministic ski-rental strategy](../ski-rental-problem/strategy.md)
- [Offline optimum for ski rental](../ski-rental-problem/opt.md)

## Proof depends on

- [Yao averaging for online algorithms](../competitive-analysis/yao-averaging-for-online-algorithms.md)

## Sources

- A. R. Karlin, M. S. Manasse, L. Rudolph and D. D. Sleator, "Competitive Snoopy Caching", Algorithmica 3, 1988.
- A. Borodin and R. El-Yaniv, "Online Computation and Competitive Analysis", Cambridge University Press, 1998.
