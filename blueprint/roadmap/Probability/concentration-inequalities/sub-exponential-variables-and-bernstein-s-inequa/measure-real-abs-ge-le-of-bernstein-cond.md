# Bernstein's inequality under the Bernstein condition

Let $X$ be a real random variable on a probability space $(\Omega, \mu)$ with every power $X^k$
integrable, $\mathbb{E}[X] = 0$ and $\mathbb{E}[X^2] = \sigma^2$, satisfying the Bernstein condition
$|\mathbb{E}[X^k]| \le \frac{1}{2} k!\, \sigma^2 b^{k-2}$ for every $k \ge 3$, with $b \ge 0$ (the
hypotheses of Bernstein's moment generating function bound). Then for every $t \ge 0$,

$$\mu(|X| \ge t) \le 2\exp\Big(-\frac{t^2}{2(\sigma^2 + bt)}\Big),$$

where the quotient is read as $0$ when $\sigma^2 + bt = 0$, giving the trivial bound $2$ (for instance
for $X = 0$, $\sigma = b = 0$ and $t = 1$).

## Sources

- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §2.1.3 (Bernstein bounds).
- A. Rinaldo, *36-755 Advanced Statistics Theory I*, Lecture 3, Carnegie Mellon University, 2017: <https://www.stat.cmu.edu/~arinaldo/Teaching/36755/F17/Scribed_Lectures/F17_0911.pdf>, Theorem 3.5.

## Background

- [Bernstein's inequality for bounded variables, two-sided](measure-real-abs-ge-le-bernstein.md): the special case $|X| \le b$.
