# Change of variables formula

If $X$ is a random element of a measurable space $(S, \mathcal S)$ with distribution $\mu$, and
$f \colon S \to \mathbb R$ is measurable with $f \ge 0$ or $E|f(X)| < \infty$, then $E f(X) = \int_S f \, d\mu$: an expected
value of a function of $X$ can be computed on the space where $X$ takes its values.

## Idea

The formula moves computations from the abstract space $\Omega$ to $S$, usually $\mathbb R^d$, where calculus is
available. If $X$ is real with a density $p$, then $E f(X) = \int f(x) p(x) \, dx$; if $X$ takes countably many values
$x_k$, then $E f(X) = \sum_k f(x_k) P(X = x_k)$. In particular $E f(X)$ depends only on the distribution of $X$. The
proof follows the construction of the integral: indicators, simple functions, increasing limits, then positive and
negative parts.

## Statements

- [Change of variables formula for expected values](expectation-change-of-variables.md)

## Background

- [Expected value](../expectation/README.md): expected values
- [Probability measures](../../probability-measures/README.md): the distribution of a random element
