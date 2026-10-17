---
article_id: af_1762aec0fad4cc3df51ff779
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: theorem_1_19_high_prob
---

# Theorem 1.19

Let $X \in \mathbb{R}^d$ be a sub-Gaussian random vector with variance proxy $\sigma^2$. Then $$\mathbb{E}\!\left[\max_{\theta \in \mathcal{B}_2} \theta^\top X\right] = \mathbb{E}\!\left[\max_{\theta \in \mathcal{B}_2} |\theta^\top X|\right] \leq 4\sigma\sqrt{d}.$$ Moreover, for any $\delta > 0$, with probability $1 - \delta$, it holds $$\max_{\theta \in \mathcal{B}_2} \theta^\top X = \max_{\theta \in \mathcal{B}_2} |\theta^\top X| \leq 4\sigma \sqrt{d} + 2\sigma \sqrt{2\log(1/\delta)}.$$

## Depends on

- [Definition 1.2](../chapter-1/002-definition-1-2.md)

## Proof depends on

- [Definition 1.17](017-definition-1-17.md)
- [Lemma 1.18](018-lemma-1-18.md)
- [Theorem 1.14](014-theorem-1-14.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Section 1.4](../../../../sources/v1/HighDimensionalStatistics.md)
