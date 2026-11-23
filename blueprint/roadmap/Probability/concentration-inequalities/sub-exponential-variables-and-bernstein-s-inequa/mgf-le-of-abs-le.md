# Bernstein's bound on the moment generating function of a bounded variable

Let $\mu$ be a probability measure and $X$ an almost everywhere measurable random variable with
$|X| \le b$ almost surely, $\mathbb{E}[X] = 0$ and $\mathbb{E}[X^2] \le \sigma^2$. For every
$t$ with $b|t| < 1$,

$$\mathbb{E}[e^{tX}] \le \exp\Big(\frac{t^2 \sigma^2}{2(1 - b|t|)}\Big).$$

A bounded variable satisfies the Bernstein condition with parameter $b$, so this is the bounded
case of the source's proposition. In particular $X$ is sub-exponential with parameters
$(\sqrt{2}\sigma, 2b)$.

## Sources

- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §2.1.3 (Bernstein bounds; bounded variables satisfy the Bernstein condition).
- A. Rinaldo, *36-755 Advanced Statistics Theory I*, Lecture 3, Carnegie Mellon University, 2017: <https://www.stat.cmu.edu/~arinaldo/Teaching/36755/F17/Scribed_Lectures/F17_0911.pdf>, Theorem 3.4.
