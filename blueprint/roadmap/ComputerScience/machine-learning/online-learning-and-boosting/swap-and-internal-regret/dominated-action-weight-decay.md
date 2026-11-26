# Multiplicative updates put bounded total weight on dominated actions, unlike general low-regret play

Let $X$ be a finite action set, $\eta, \varepsilon > 0$ and losses $\ell_t \in \mathbb{R}^X$.

1. (Hedge.) If action $j$ is $\varepsilon$-dominated by a fixed mixed strategy $y$, i.e. $\sum_i y(i)\ell_s(i) + \varepsilon \le \ell_s(j)$ for all $s < T$, then Hedge with rate $\eta$ satisfies $\sum_{t<T} p_t(j) \le 1/(1 - e^{-\eta\varepsilon})$.
2. (Polynomial weights.) If all factors $1 - \eta\ell_s(i)$ are positive and some action $k$ has $0 \le \ell_s(k)$ and $\ell_s(k) + \varepsilon \le \ell_s(j)$ for all $s<T$, then multiplicative weights satisfies $\sum_{t<T} p_t(j) \le 1/(\eta\varepsilon)$.
3. (No such guarantee from regret alone.) For every $\varepsilon \in [0,1/2]$ and $m$, there are deterministic plays and $[0,1]$ losses on three actions over $2m$ rounds in which action $2$ is $\varepsilon$-dominated by action $0$ in every round, the external regret is at most $0$, and action $2$ is played $m$ times.

## Proof sketch

For Hedge, the ratio of $j$'s weight to the $y$-weighted geometric mean of the weights decays by $e^{-\eta\varepsilon}$ per round, and that geometric mean is at most the total weight, so $p_t(j) \le e^{-\eta\varepsilon t}$; sum the geometric series. For polynomial weights compare $j$ with $k$ directly using $(1-\eta a)/(1 - \eta b) \le 1 - \eta(a - b)$. The counterexample alternates rounds so that action $2$ is played half the time while losses are arranged so no fixed action beats the play.

## Depends on

- [Multiplicative weights (polynomial weights) algorithm](../regret-in-the-experts-setting/polynomial-weights-algorithm.md)
- [The Hedge loss bound](../hedge-algorithm/alg-loss-le.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4.
