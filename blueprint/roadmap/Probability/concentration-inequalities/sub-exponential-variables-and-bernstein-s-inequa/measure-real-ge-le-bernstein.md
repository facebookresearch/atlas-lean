# Bernstein's inequality for bounded variables, upper tail

Let $\mu$ be a probability measure and $X$ an almost everywhere measurable random variable with
$|X| \le b$ almost surely for some $b \ge 0$, $\mathbb{E}[X] = 0$ and
$\mathbb{E}[X^2] \le \sigma^2$. For every $t \ge 0$,

$$\mu(X \ge t) \le \exp\Big(-\frac{t^2}{2(\sigma^2 + bt)}\Big).$$

When $\sigma^2 + bt = 0$ the right-hand side is read as $1$.

## Sources

- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §2.1.3 (Bernstein bounds).
- A. Rinaldo, *36-755 Advanced Statistics Theory I*, Lecture 3, Carnegie Mellon University, 2017: <https://www.stat.cmu.edu/~arinaldo/Teaching/36755/F17/Scribed_Lectures/F17_0911.pdf>, Theorem 3.5.

## Background

- [Hoeffding's inequality](../hoeffding-s-inequality/README.md): Bernstein's bound replaces the range $b^2$ by the variance $\sigma^2$ in the Gaussian regime.
