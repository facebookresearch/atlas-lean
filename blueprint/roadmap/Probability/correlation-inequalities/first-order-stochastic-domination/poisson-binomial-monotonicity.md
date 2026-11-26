# Stochastic monotonicity of Poisson-binomial and binomial laws

For a list $p = (p_1, \dots, p_m) \in [0,1]^m$ let $\mathrm{PB}(p)$ denote the Poisson-binomial law of the number of successes in independent Bernoulli($p_i$) trials. Then:

1. if $p_i \le q_i$ for every $i$, then $\mathrm{PB}(p) \preceq_{\mathrm{st}} \mathrm{PB}(q)$; adding trials increases the law; in particular $\mathrm{Bin}(m, p) \preceq_{\mathrm{st}} \mathrm{Bin}(m, q)$ for $p \le q$ and $\mathrm{Bin}(m, p) \preceq_{\mathrm{st}} \mathrm{Bin}(n, p)$ for $m \le n$;
2. if every $p_i \ge p$ then $\mathrm{Bin}(m, p) \preceq_{\mathrm{st}} \mathrm{PB}(p_1, \dots, p_m)$, and if every $p_i \le p$ then $\mathrm{PB}(p_1,\dots,p_m) \preceq_{\mathrm{st}} \mathrm{Bin}(m,p)$;
3. (waiting-time series) for $p \in (0,1]$ and $r \in \mathbb{N}$, $\sum_{t=0}^{\infty} \Pr[\mathrm{Bin}(t, p) < r] = r/p$.

## Proof sketch

A Bernoulli($q$) coin dominates a Bernoulli($p$) coin when $p \le q$, and domination is closed under independent sums, giving items 1 and 2. For item 3, $\sum_t \Pr[\mathrm{Bin}(t,p) < r]$ is the expected number of trials up to and including the $r$-th success in an infinite Bernoulli sequence, which is $r/p$ by linearity over the $r$ geometric waiting times.

## Depends on

- [First-order stochastic domination](first-order-stochastic-domination.md)
- [Poisson-binomial mass function](../../distributions/discrete/poisson-binomial-distribution/poisson-binomial-law/poisson-binomial-pmf.md)

## Proof depends on

- [Characterizations and closure properties of stochastic domination](stochastic-domination-characterizations.md)

## Sources

- D. A. Levin and Y. Peres, "Markov Chains and Mixing Times", American Mathematical Society, 2nd ed., 2017.
- M. Mitzenmacher and E. Upfal, "Probability and Computing: Randomization and Probabilistic Techniques in Algorithms and Data Analysis", Cambridge University Press, 2nd ed., 2017.
