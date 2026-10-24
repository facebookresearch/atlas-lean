---
article_id: af_8266056aa27f280cb9aa20f8
declaration: theorem
origin: cited
lean: Chapter3.cor_3_16
---

# Corollary 3.16

Fix $\beta \geq (1+\sqrt{5})/4 \approx 0.81$, $Q > 0$, $\delta > 0$ and $n$ large enough to ensure $n-1 \geq \lceil n^{1/(2\beta+1)} \rceil$, assume the general regression model (3.1) with $f \in \Theta(\beta, Q)$ and $\varepsilon \sim \mathsf{subG}_n(\sigma^2)$, $\sigma^2 \leq 1$. Let $\{\varphi_j\}_{j=1}^{n-1}$ be the trigonometric basis. Denote by $\varphi_{\hat{\theta}^{\mathrm{BIC}}}^{n-1}$ (resp. $\varphi_{\hat{\theta}^{\mathrm{L}}}^{n-1}$) the BIC (resp. Lasso) estimator defined in (3.3) (resp. (3.4)) over $\mathbb{R}^{n-1}$ with regularization parameter given by (3.5) (resp. (3.6)). Then $\varphi_{\hat{\theta}}^{n-1}$, where $\hat{\theta} \in \{\hat{\theta}^{\mathrm{BIC}}, \hat{\theta}^{\mathrm{L}}\}$ satisfies with probability $1-\delta$, $$\|\varphi_{\hat{\theta}}^{n-1} - f\|_{L_2([0,1])}^2 \lesssim n^{-2\beta/(2\beta+1)} + \sigma^2 \log(1/\delta)/n.$$ Moreover, $\mathbb{E}\|\varphi_{\hat{\theta}}^{n-1} - f\|_{L_2([0,1])}^2 \lesssim \sigma^2 (\log n / n)^{2\beta/(2\beta+1)}$, where constant factors may depend on $\beta$ and $Q$.

## Depends on

- [Definition 1.2](../chapter-1/002-definition-1-2.md)
- [Theorem 3.4](039-theorem-3-4.md)
- [Theorem 3.5](040-theorem-3-5.md)
- [Theorem 3.11](044-theorem-3-11.md)

## Proof depends on

- [Lemma 3.13](046-lemma-3-13.md)
- [Lemma 3.14](047-lemma-3-14.md)

## Sources

- [MIT 18.S997 High-Dimensional Statistics (Spring 2015), Chapter 3, Section on Adaptive estimation](../../../../sources/v1/HighDimensionalStatistics.md)
