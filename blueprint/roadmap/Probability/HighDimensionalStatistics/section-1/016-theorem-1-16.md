---
article_id: af_46b546cca67e2395df8f8415
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: SubGaussianPolytope.theorem_1_16
---

# Theorem 1.16

Let $\mathsf{P}$ be a polytope with $N$ vertices $v^{(1)}, \ldots, v^{(N)} \in \mathbb{R}^d$ and let $X \in \mathbb{R}^d$ be a random vector such that $[v^{(i)}]^\top X$, $i = 1, \ldots, N$ are sub-Gaussian random variables with variance proxy $\sigma^2$. Then $$\mathbb{E}\!\left[\max_{\theta \in \mathsf{P}} \theta^\top X\right] \leq \sigma \sqrt{2 \log(N)}, \quad \text{and} \quad \mathbb{E}\!\left[\max_{\theta \in \mathsf{P}} |\theta^\top X|\right] \leq \sigma \sqrt{2 \log(2N)}.$$ Moreover, for any $t > 0$, $$\mathbb{P}\!\left(\max_{\theta \in \mathsf{P}} \theta^\top X > t\right) \leq N e^{-t^2/(2\sigma^2)}, \quad \text{and} \quad \mathbb{P}\!\left(\max_{\theta \in \mathsf{P}} |\theta^\top X| > t\right) \leq 2N e^{-t^2/(2\sigma^2)}.$$

## Depends on

- [Definition 1.2](../chapter-1/002-definition-1-2.md)

## Proof depends on

- [Lemma 1.15](015-lemma-1-15.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Section 1.4](../../../../sources/v1/HighDimensionalStatistics.md)
