# Majority from pairwise independent votes

Let $X_1, \dots, X_m$ ($m \ge 1$) be pairwise independent random variables with values in $[0, 1]$ and $\mathbb{E}[X_i] \ge \frac12 + \varepsilon$ for some $\varepsilon > 0$. Then

$$
\Pr\Big[\sum_{i=1}^m X_i \le \frac{m}{2}\Big] \le \frac{1}{4\varepsilon^2 m}.
$$

In particular, pairwise independent Boolean votes, each correct with probability at least $\frac12 + \varepsilon$, fail to have a strict correct majority (ties count as failures) with probability at most $1/(4\varepsilon^2 m)$.

## Proof sketch

Each $X_i$ has variance at most $1/4$, and pairwise independence makes the variance of the sum at most $m/4$. The sum's mean is at least $m/2 + \varepsilon m$, so failure requires a deviation of at least $\varepsilon m$, which Chebyshev's inequality bounds by $(m/4)/(\varepsilon m)^2$.

## Depends on

- [Variance of the sample mean under pairwise independence](../../laws-of-large-numbers/variance-sample-mean-of-pairwise.md)

## Proof depends on

- [Chebyshev's inequality](../../moments/chebyshev-s-inequality/meas-ge-le-variance-div-sq.md)
- [Variance of the sample mean under pairwise independence](../../laws-of-large-numbers/variance-sample-mean-of-pairwise.md)

## Sources

- L. Trevisan, "CS276 Lecture 12: Goldreich-Levin", lecture notes, UC Berkeley, 2009.
- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
