# Multiplicative updates put bounded total weight on dominated actions, unlike general low-regret play

Let $X$ be a finite action set and $\varepsilon > 0$. An action $j$ is $\varepsilon$-dominated by an action $k$ (or by a mixed action $y$) if in every round the loss of $j$ is at least $\varepsilon$ plus the loss of $k$ (or plus the $y$-expected loss) (Blum and Mansour, Section 4.4.4). A player who plays Randomized Weighted Majority (Hedge) or Polynomial Weights gives $\varepsilon$-dominated actions small weight, whereas there are cases in which the external regret of a player is small, yet it gives $\varepsilon$-dominated actions high weight (Blum and Mansour, Exercise 4.8).

## Proof sketch

Derived (not stated in the cited source, which poses these claims as an exercise): the total weight $\sum_{t<T} p_t(j)$ on an $\varepsilon$-dominated action stays bounded independently of the horizon $T$. Let $\eta > 0$ and losses $\ell_t \in \mathbb{R}^X$.

1. (Hedge.) If $\sum_i y(i)\ell_s(i) + \varepsilon \le \ell_s(j)$ for a fixed mixed strategy $y$ and all $s < T$, then Hedge with rate $\eta$ satisfies $\sum_{t<T} p_t(j) \le 1/(1 - e^{-\eta\varepsilon})$: the ratio of $j$'s weight to the $y$-weighted geometric mean of the weights decays by $e^{-\eta\varepsilon}$ per round, and that geometric mean is at most the total weight, so $p_t(j) \le e^{-\eta\varepsilon t}$; sum the geometric series.
2. (Polynomial weights.) If all factors $1 - \eta\ell_s(i)$ are positive and some action $k$ has $0 \le \ell_s(k)$ and $\ell_s(k) + \varepsilon \le \ell_s(j)$ for all $s<T$, then multiplicative weights satisfies $\sum_{t<T} p_t(j) \le 1/(\eta\varepsilon)$, comparing $j$ with $k$ through $(1-\eta a)/(1 - \eta b) \le 1 - \eta(a - b)$.
3. (No such guarantee from regret alone.) For every $\varepsilon \in [0,1/2]$ and $m$, there are deterministic plays and $[0,1]$ losses on three actions over $2m$ rounds in which action $2$ is $\varepsilon$-dominated by action $0$ in every round, the external regret is at most $0$, and action $2$ is played $m$ times: alternate rounds so that action $2$ is played half the time while the losses are arranged so that no fixed action beats the play.

## Depends on

- [Multiplicative weights (polynomial weights) algorithm](../regret-in-the-experts-setting/polynomial-weights-algorithm.md)
- [The Hedge loss bound](../hedge-algorithm/alg-loss-le.md)

## Sources

- Avrim Blum and Yishay Mansour, "Learning, Regret Minimization, and Equilibria", in N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press, 2007, Chapter 4, Section 4.4.4 and Exercise 4.8.
