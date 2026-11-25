# The Beta-coalescent on a finite sample

Let $0 < \alpha < 2$ and let $\Lambda$ be the [Beta$(2 - \alpha, \alpha)$-coalescent measure](beta-lambda.md). The [Λ-coalescent rate matrix](../../coalescents/the-coalescent-rate-matrix-on-partitions-of-a-fi.md) $Q^\Lambda_n$ on the partitions of $\{1, \dots, n\}$
merges each given set of $k$ of the $b$ current blocks at the [closed-form rate](merger-rate-beta-lambda.md)

$$\lambda_{b,k} = \frac{B(k - \alpha,\, b - k + \alpha)}{B(2 - \alpha,\, \alpha)} \qquad (2 \le k \le b).$$

It is an exchangeable rate matrix, lumpable to its block-counting chain, and the [path laws are consistent under restriction](../../coalescents/path-laws-of-the-coalescent-on-a-finite-sample-a.md). The block-counting chain jumps from $b$ to $b - k + 1$
with probability $\binom bk \lambda_{b,k} / \lambda_b$, where $\lambda_b = \sum_{k=2}^b \binom bk \lambda_{b,k}$. From three blocks, $\lambda_{3,2} = \alpha/2$ and $\lambda_{3,3} = 1 - \alpha/2$, so $\lambda_3 = 1 + \alpha$ and

$$\mathbb P(3 \to 2) = \frac{3\alpha}{2(1 + \alpha)}, \qquad \mathbb P(3 \to 1) = \frac{2 - \alpha}{2(1 + \alpha)} .$$

For $\alpha = 1$, $\Lambda$ is the uniform measure and the chain is the Bolthausen–Sznitman coalescent, with $\lambda_{b,k} = (k - 2)!\,(b - k)!/(b - 1)!$.

## Depends on

- [The Λ-coalescent rate matrix on partitions of a finite sample](../../coalescents/the-coalescent-rate-matrix-on-partitions-of-a-fi.md)
- [Closed form of the Beta-coalescent rates](merger-rate-beta-lambda.md)

## Related topics

- [Path laws of the Λ-coalescent on a finite sample are consistent under restriction](../../coalescents/path-laws-of-the-coalescent-on-a-finite-sample-a.md)

## Sources

- N. Berestycki, "Recent progress in coalescent theory", arXiv:0909.3985 (2009), Theorem 3.1 and Examples 2–3, equations (53), (62), (63).
