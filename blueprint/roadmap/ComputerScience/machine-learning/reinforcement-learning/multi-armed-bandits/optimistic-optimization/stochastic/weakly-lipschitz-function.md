# Weakly Lipschitz function

Let $\ell$ be a [dissimilarity](dissimilarity.md) on a measurable space $\mathcal X$ and $f$ the mean-payoff function of
a Markov kernel from $\mathcal X$ to $[0, 1]$ (see [noisy evaluations](noisy-evaluations.md)), with
$f^* = \sup_{\mathcal X} f$. The function $f$ is *weakly Lipschitz* with respect to $\ell$ if, for all
$x, y \in \mathcal X$,

$$
f^* - f(y) \le f^* - f(x) + \max\{f^* - f(x), \ \ell(x, y)\}.
$$

Equivalently, $f(x) - f(y) \le \max\{f^* - f(x), \ell(x, y)\}$ for all $x$ and $y$. If
$\lvert f(x) - f(y) \rvert \le \ell(x, y)$ for all $x, y$, then $f$ is weakly Lipschitz. At a point $x^*$ with
$f(x^*) = f^*$ the condition reads $f^* - f(y) \le \ell(x^*, y)$ for every $y$, so when $\ell$ is a
[semi-metric](../semi-metric.md) and $f$ attains its maximum, a weakly Lipschitz $f$ is
[locally smooth around a maximizer](../local-smoothness-around-a-maximizer.md). Around a point $x$ that is
$\varepsilon$-optimal, the condition gives $f(y) \ge f^* - 2\varepsilon$ when $\ell(x, y) \le \varepsilon$: it rules out
sudden large drops near near-optimal points, and $f$ may still be discontinuous.

## Sources

- S. Bubeck, R. Munos, G. Stoltz and Cs. Szepesvári, *X-armed bandits*, Journal of Machine Learning Research 12
  (2011), 1655–1695, <https://jmlr.org/papers/v12/bubeck11a.html>, Section 4.1, Assumption A2, equations (4) and (5).
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 3.4.2, Assumption 5 and Remark 3.6.

## Depends on

- [Dissimilarity](dissimilarity.md)
- [Noisy evaluations](noisy-evaluations.md)
