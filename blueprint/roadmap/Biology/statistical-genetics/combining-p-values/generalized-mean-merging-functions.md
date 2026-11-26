# Merging p-values by generalized means

For a continuous strictly monotonic $\phi : [0, 1] \to [-\infty, \infty]$ with inverse $\psi$, the Kolmogorov mean is $M_{\phi,K}(p_1, \dots, p_K) = \psi\bigl(\tfrac1K \sum_{k=1}^K \phi(p_k)\bigr)$ (Eq. (7)); $\phi(u) = u^r$ gives the power mean $M_{r,K}(p) = \bigl(\tfrac1K \sum_k p_k^r\bigr)^{1/r}$ for $r \ne 0$, with $M_{0,K}$ the geometric mean, $M_{\infty,K} = \max$ and $M_{-\infty,K} = \min$ (Eq. (8)).

**Theorem** (Theorem 2 of the source). If $\phi$ is integrable, $\int_0^1 |\phi(u)|\, du < \infty$, then for every $K \ge 2$, every $\epsilon > 0$ and all p-variables $p_1, \dots, p_K$ with arbitrary dependence,

$$\mathbb P\Bigl( M_{\phi,K}(p_1, \dots, p_K) \le \psi\Bigl( \frac1\epsilon \int_0^\epsilon \phi(u)\, du \Bigr) \Bigr) \le \epsilon. \tag{11}$$

**Corollaries.**
- For $r \in (-1, \infty]$, $(r + 1)^{1/r} M_{r,K}$ is a merging function for every $K$, and the family is asymptotically precise (Proposition 3); here $(r+1)^{1/r}$ means $e$ at $r = 0$ and $1$ at $r = \infty$. So twice the arithmetic mean and $e$ times the geometric mean are valid p-values.
- For $r \in (-1, \infty)$ and $K \ge 2$, $(r + 1)^{1/r} M_{r,K}$ is precise if and only if $r \in [\tfrac{1}{K-1}, K - 1]$ (Proposition 4). In particular $2 M_{1,K}$ is precise for all $K \ge 2$.
- For $r \ge 1$, $\min(r + 1, K)^{1/r} M_{r,K}$ is a precise merging function (Proposition 5).

## Depends on

- [p-value merging functions](p-value-merging-function.md)

## Expansion

With $\phi(u) = u^r$, $r > -1$, the threshold in (11) is $\bigl(\epsilon^r/(r+1)\bigr)^{1/r} = \epsilon (r + 1)^{-1/r}$, which gives Proposition 3. The bound (11) is proved with robust risk aggregation results on the smallest possible quantile of an average of identically distributed variables under arbitrary dependence; the threshold involves the average of $\phi$ over the lowest $\epsilon$-tail of the uniform law. Precision and asymptotic precision come from matching extremal dependence structures (Appendix A).

## Sources

- V. Vovk and R. Wang, Combining p-values via averaging, Biometrika 107 (2020). <https://doi.org/10.1093/biomet/asaa027>; numbering follows the preprint <https://arxiv.org/abs/1212.4966> (version 5).
