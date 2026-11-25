# Uniform integrability

A family of random variables $\{X_i\}_{i \in I}$ is uniformly integrable if
$\sup_{i \in I} E(|X_i| ; |X_i| > M) \to 0$ as $M \to \infty$: large values contribute little to the expected absolute
value, uniformly over the family.

## Idea

Choosing $M$ with $\sup_i E(|X_i| ; |X_i| > M) < 1$ gives $\sup_i E|X_i| \le M + 1$, so a uniformly
integrable family is bounded in $L^1$. The converse fails: on $(0, 1)$ with Lebesgue measure, $X_n = n 1_{(0, 1/n)}$ has
$E X_n = 1$ for every $n$, but $E(X_n ; X_n > M) = 1$ whenever $n > M$. A family dominated by one integrable random
variable is uniformly integrable, and so is a family bounded in $L^p$ for some $p > 1$. Uniform integrability is what
turns convergence in probability into convergence in $L^1$, and for martingales it is equivalent to convergence in
$L^1$.

## Statements

- [Uniform integrability](uniform-integrability.md)

## Background

- [Expected value](../../foundations/laws-of-random-variables-and-identical-distribut/expectation/README.md): expected values
