# Chebyshev's inequality

A square-integrable real random variable $X$ is at distance at least $c > 0$ from its mean with probability at most
$\operatorname{var}(X) / c^2$:

$$P(|X - EX| \ge c) \le \frac{\operatorname{var}(X)}{c^2}.$$

The same holds for every finite measure $\mu$ in place of $P$, with $EX = \int X \, d\mu$ and
$\operatorname{var}(X) = \int (X - EX)^2 \, d\mu$.

## Idea

On the event $\{|X - EX| \ge c\}$ the nonnegative random variable $(X - EX)^2 / c^2$ is at least $1$, so the probability
of the event is at most the expected value of $(X - EX)^2 / c^2$, which is $\operatorname{var}(X) / c^2$. The bound is
attained: if $X$ takes the values $-c$ and $c$ with probability $\frac12$ each, both sides equal $1$. It turns a
variance estimate into a deviation estimate; with the variance of a sum, it proves the L² weak law of large numbers.

## Statements

- [Chebyshev's inequality](meas-ge-le-variance-div-sq.md)

## Background

- [Expected value](../../foundations/laws-of-random-variables-and-identical-distribut/expectation/README.md): expected values

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Theorem 1.6.4 and the remark after it, inequality (1.6.1),
  applied to $X - EX$ (version read: the author's January 2019 PDF).
