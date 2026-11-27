# Law of the iterated logarithm

Let $X_0, X_1, \dots$ be independent, identically distributed, measurable real random variables on a probability space with $\mathbb{E}[X_0^2] < \infty$, $\mathbb{E}[X_0] = 0$ and $\operatorname{Var}(X_0) = 1$, and let $S_n = X_0 + \dots + X_{n-1}$. Then almost surely $\limsup_{n \to \infty} S_n / \sqrt{2 n \log \log n} = 1$ and $\liminf_{n \to \infty} S_n / \sqrt{2 n \log \log n} = -1$.

## Idea

The strong law says $S_n / n \to 0$, and the central limit theorem says that $S_n / \sqrt{n}$ is close to standard normal in distribution. The law of the iterated logarithm describes the largest fluctuations along a single path: for every $\varepsilon > 0$, $S_n$ exceeds $(1 - \varepsilon)\sqrt{2 n \log \log n}$ infinitely often but $(1 + \varepsilon)\sqrt{2 n \log \log n}$ only finitely often. The extra factor $\sqrt{2 \log \log n}$ grows very slowly. The proof looks along geometric times $n_k \approx \theta^k$. For the upper bound, Gaussian-type tail bounds $P(S_n > x \sqrt{n}) \approx e^{-x^2/2}$, a maximal inequality and the first Borel–Cantelli lemma suffice after truncating the variables (Hartman and Wintner). For the lower bound, the increments over disjoint blocks are independent, and the second Borel–Cantelli lemma applies once their tails are bounded from below at levels of order $\sqrt{\log \log n}$ standard deviations. Convergence in distribution alone does not give such bounds, since the level grows with $n$; they come from a quantitative form of the central limit theorem or from truncation and exponential estimates.

## Statements

- [Law of the iterated logarithm](law-of-the-iterated-logarithm.md)
- [Law of the iterated logarithm, square-integrable form](law-of-the-iterated-logarithm-of-mem-lp.md): square-integrable form

## Sources

- P. Hartman and A. Wintner, "On the law of the iterated logarithm", *American Journal of Mathematics* (1941).
