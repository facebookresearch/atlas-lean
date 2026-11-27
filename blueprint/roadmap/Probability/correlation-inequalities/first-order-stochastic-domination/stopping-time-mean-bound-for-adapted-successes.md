# Mean bound for stopping times triggered by adapted successes

Let $(\mathcal{F}_t)_{t\ge0}$ be a filtration, $A_t \in \mathcal F_{t+1}$ events, $N_n = \sum_{t<n}\mathbf 1_{A_t}$, and $r \in \mathbb{N}$, $p \in (0, 1]$. Let $\tau$ be a stopping time with values in $\mathbb{N}\cup\{\infty\}$ such that $\tau \le n$ whenever $N_n \ge r$, and suppose $\Pr[A_t \mid \mathcal{F}_t] \ge p$ almost surely on $\{t < \tau\}$. Then $\tau < \infty$ almost surely, $\tau$ is integrable, and

$$
\mathbb{E}[\tau] \le \frac{r}{p}.
$$

In particular the first time $\tau_r$ at which $N_{\tau_r} \ge r$ satisfies $\mathbb{E}[\tau_r] \le r/p$ whenever the conditional success probability is at least $p$ while fewer than $r$ successes have occurred.

## Proof sketch

Write $\mathbb{E}[\tau] = \sum_{n \ge 0}\Pr[\tau > n]$ (tail-sum formula). On $\{\tau > n\}$ fewer than $r$ events occurred among the first $n$, so by the active-before-target domination $\Pr[\tau > n] \le \Pr[\mathrm{Bin}(n, p) < r]$. Summing and applying the waiting-time series gives $r/p$, and finiteness of the series gives $\tau < \infty$ almost surely.

## Depends on

- [Martingales, submartingales and supermartingales](../../martingales/martingales-submartingales-and-supermartingales/martingale.md)

## Proof depends on

- [Poisson-binomial domination of adapted event counts](adapted-event-count-domination.md)
- [Stochastic monotonicity of Poisson-binomial and binomial laws](poisson-binomial-monotonicity.md)

## Sources

- D. A. Levin and Y. Peres, "Markov Chains and Mixing Times", American Mathematical Society, 2nd ed., 2017.
- M. Mitzenmacher and E. Upfal, "Probability and Computing: Randomization and Probabilistic Techniques in Algorithms and Data Analysis", Cambridge University Press, 2nd ed., 2017.
