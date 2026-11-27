# Expected value

The expected value of a real random variable $X$ on a probability space $(\Omega, \mathcal F, P)$ is its integral
$EX = \int X \, dP$. For $X \ge 0$ it always exists in $[0, \infty]$; in general $EX = EX^+ - EX^-$ is defined when at
least one of the two terms is finite, in particular when $E|X| < \infty$.

## Idea

Because the expected value is an integral, it is linear on integrable random variables,
$E(aX + bY) = a\,EX + b\,EY$, additive on nonnegative ones, and monotone, and it obeys the convergence theorems of
integration. Linearity needs finite expectations: if $U$ is uniform on $(0, 1)$, then $X = 1/U$ has $EX = \infty$ and
$E(-X) = -\infty$, while $X + (-X) = 0$ has mean $0$. For a fair die, $EX = (1 + 2 + \dots + 6)/6 = 7/2$. A mean can be infinite, or fail to exist: for the
Cauchy distribution both $EX^+$ and $EX^-$ are infinite, so $EX$ is not defined.

## Statements

- [Expected value of a random variable](expectation-random-variable.md)

## Background

- [Probability measures](../../probability-measures/README.md): probability spaces
