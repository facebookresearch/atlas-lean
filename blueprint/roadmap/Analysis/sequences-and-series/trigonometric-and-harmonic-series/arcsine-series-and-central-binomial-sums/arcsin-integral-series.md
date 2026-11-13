# Integrated arcsine series

Let $c_n = \binom{2n}{n}/4^n$. For real $t$, the integrated
arcsine series is

$$F(t) = \sum_{n=0}^{\infty} \frac{c_n\, t^{2n+1}}{(2n+1)^2},$$

with the convention that the sum is $0$ when the series is not summable.

Each term is the antiderivative vanishing at $0$ of the corresponding term $c_n t^{2n}/(2n+1)$
of $S(t)/t$, where $S(t) = \sum_{n \ge 0} c_n t^{2n+1}/(2n+1)$ is the arcsine Taylor series.
