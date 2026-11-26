# Poisson-binomial domination of adapted event counts

Let $(\mathcal{F}_t)_{t \ge 0}$ be a filtration on a probability space, let $A_t$ be events with $A_t \in \mathcal{F}_{t+1}$, and let $N_n = \sum_{t<n}\mathbf 1_{A_t}$ be the number of events among the first $n$. Let $p = (p_0, \dots, p_{n-1}) \in [0,1]^n$.

1. If $\Pr[A_t \mid \mathcal F_t] \ge p_t$ almost surely for every $t < n$, then $\mathrm{law}(N_n)$ stochastically dominates $\mathrm{PB}(p)$; if $\Pr[A_t\mid\mathcal F_t] \le p_t$ almost surely for every $t<n$, then $\mathrm{PB}(p)$ dominates $\mathrm{law}(N_n)$.
2. (Active before target) For $r \in \mathbb{N}$, if $\Pr[A_t\mid\mathcal F_t] \ge p_t$ holds almost surely on the event $\{N_t < r\}$, then $\min(N_n, r)$ dominates $\min(Z, r)$ for $Z \sim \mathrm{PB}(p)$; in particular, with $p_t \equiv p$, $\Pr[N_n < r] \le \Pr[\mathrm{Bin}(n,p) < r]$.

The same statements hold for finite-horizon adaptive discrete processes with history-dependent events, assuming the conditional bounds only at histories of positive probability.

## Proof sketch

Construct a monotone coupling step by step: at time $t$ sample the event using a uniform $U_t$ thresholded at its conditional probability, and the independent Bernoulli($p_t$) trial as $\{U_t \le p_t\}$. Under the lower envelope each trial success implies the event, so the count dominates pathwise, and pathwise domination yields stochastic domination. For the capped version only steps with fewer than $r$ events need the envelope, since once $r$ events occurred both capped counts are at $r$.

## Depends on

- [First-order stochastic domination](first-order-stochastic-domination.md)
- [Poisson-binomial mass function](../../distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-pmf.md)
- [Martingales, submartingales and supermartingales](../../martingales/martingales-submartingales-and-supermartingales/martingale.md)

## Proof depends on

- [Stochastic monotonicity of Poisson-binomial and binomial laws](poisson-binomial-monotonicity.md)
- [Characterizations and closure properties of stochastic domination](stochastic-domination-characterizations.md)

## Sources

- D. A. Levin and Y. Peres, "Markov Chains and Mixing Times", American Mathematical Society, 2nd ed., 2017.
- M. Mitzenmacher and E. Upfal, "Probability and Computing: Randomization and Probabilistic Techniques in Algorithms and Data Analysis", Cambridge University Press, 2nd ed., 2017.
