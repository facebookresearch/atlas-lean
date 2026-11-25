# Convergence in distribution to a constant

Let $E$ be a pseudometric space with its Borel $\sigma$-algebra, let $(\Omega, P)$ be a probability space, and let $X_i : \Omega \to E$ be indexed along a limit (a sequence $n \to \infty$ or, more generally, a filter). If the $X_i$ converge in distribution to the constant $c \in E$ (with the constant viewed as a random variable on any probability space), then they converge to $c$ in probability: $P(d(X_i, c) \ge \varepsilon) \to 0$ for every $\varepsilon > 0$.

## Idea

Convergence in probability implies convergence in distribution, but not conversely in general: convergence in distribution only concerns laws, and the variables may even live on different spaces. A constant limit is the exception, because its law is a point mass. By the portmanteau theorem applied to the closed set $\{x : d(x, c) \ge \varepsilon\}$, $\limsup P(d(X_i, c) \ge \varepsilon)$ is at most the mass the point mass at $c$ gives to that set, which is $0$. This is the step behind Slutsky's theorem: if $X_n$ converges in distribution to $X$ and $Y_n$ to a constant $c$, then $(X_n, Y_n)$ converges in distribution to $(X, c)$, so sums and products behave as expected; the delta method rests on it.

## Statements

- [Convergence in distribution to a constant implies convergence in probability](tendsto-in-measure-of-tendsto-in-distrib.md)
- [Delta method](delta-method.md): an application, whose proof uses the main statement
- [Delta method in one dimension](delta-method-real.md): the delta method for real random variables
- [Studentization with a consistent covariance estimator](studentization-for-an-explicitly-supplied-depend.md): an application of Slutsky's theorem, normalizing an asymptotically normal vector by a consistent covariance estimator
- [Slutsky's theorem for a random matrix times a random vector](slutsky-s-theorem-for-a-random-matrix-times-a-random-vector.md)
