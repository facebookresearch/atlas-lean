# Cumulative pseudo-regret

Consider the [interaction](noisy-evaluations.md) of a strategy with budget $n$ and a Markov kernel $\nu$ from
$\mathcal X$ to $[0, 1]$, with mean-payoff function $f$ and $f^* = \sup_{\mathcal X} f$. The *cumulative pseudo-regret*
after $n$ rounds is the random variable

$$
R_n = n f^* - \sum_{t=1}^{n} f(X_t) \ge 0.
$$

As $\mathbb E[Y_t] = \mathbb E[\mathbb E[Y_t \mid H_{t-1}, X_t]] = \mathbb E[f(X_t)]$, the expected pseudo-regret
$\mathbb E[R_n]$ equals the expected cumulative regret $n f^* - \mathbb E\big[\sum_{t=1}^n Y_t\big]$. Recommending
$X_T$ with $T$ drawn uniformly from $\{1, \dots, n\}$, independently of the rest, gives an expected
[loss](../loss.md) $\mathbb E[f^* - f(X_T)] = \mathbb E[R_n]/n$ when $f$ attains its maximum.

## Sources

- S. Bubeck, R. Munos, G. Stoltz and Cs. Szepesvári, *X-armed bandits*, Journal of Machine Learning Research 12
  (2011), 1655–1695, <https://jmlr.org/papers/v12/bubeck11a.html>, Section 2 and Remark 1.
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 3.4.2, equations (3.13) and (3.14).

## Depends on

- [Noisy evaluations](noisy-evaluations.md)
- [Sum over a finite set](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum.md)
