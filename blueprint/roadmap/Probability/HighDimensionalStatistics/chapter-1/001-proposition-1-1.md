---
article_id: af_9c4bcd7f845028bf387c1750
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: GaussianTailBound.gaussian_tail_bound
---

# Proposition 1.1

Let $X$ be a Gaussian random variable with mean $\mu$ and variance $\sigma^2$. Then for any $t > 0$, it holds $\mathbb{P}(X - \mu > t) \leq \frac{1}{\sqrt{2\pi}} \cdot \frac{e^{-t^2/(2\sigma^2)}}{t}$. By symmetry we also have $\mathbb{P}(X - \mu < -t) \leq \frac{1}{\sqrt{2\pi}} \cdot \frac{e^{-t^2/(2\sigma^2)}}{t}$, and $\mathbb{P}(|X - \mu| > t) \leq \sqrt{\frac{2}{\pi}} \cdot \frac{e^{-t^2/(2\sigma^2)}}{t}$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Chapter 1, Section 1.1](../../../../sources/v1/HighDimensionalStatistics.md)
