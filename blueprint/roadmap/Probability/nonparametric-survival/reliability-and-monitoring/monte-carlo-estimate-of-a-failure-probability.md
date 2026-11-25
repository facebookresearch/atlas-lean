# Monte Carlo estimate of a failure probability

Let $n\ge1$ and let $X_1,\dots,X_n$ be independent, identically distributed random vectors of basic structural variables on a common
probability space, with measurable limit-state function $g$, and let
$p = P(g(X_1) \le 0)$ the failure probability. The estimate $\hat p = \frac1n \sum_{i=1}^n \mathbf 1\{g(X_i) \le 0\}$ satisfies, for every
$\varepsilon > 0$,

$$P\bigl(\lvert \hat p - p\rvert > \varepsilon\bigr) \le 2 e^{-2\varepsilon^2 n},$$

since the indicators are independent Bernoulli variables with the same mean $p$. For $0<\delta<1$, the bound guarantees error probability
at most $\delta$ when $n\ge \log(2/\delta)/(2\varepsilon^2)$. Absolute-error control need not be useful relative-error control when $p$
is small; relative-error guarantees, importance sampling and variance reduction are outside this result.

## Depends on

## Proof depends on

- [Two-sided Hoeffding inequality for Bernoulli sums](../../concentration-inequalities/hoeffding-s-inequality/hoeffding-bernoulli-sum-abs-tail.md)

## Sources

- W. Hoeffding, "Probability inequalities for sums of bounded random variables", *Journal of the American Statistical Association* 58 (1963), 13–30, Theorem 2.
