# Measure Mutual Information prod eq zero

Let $X$ and $Y$ be measurable spaces and let $P$ and $R$ be probability measures on $X$ and $Y$. The product law $P \otimes R$ on $X \times Y$ has zero mutual information:

$$I(P \otimes R) = \frac{D_{\mathrm{KL}}(P \otimes R \parallel P \otimes R)}{\ln 2} = 0.$$

For example, for $\sigma^2 \ge 0$ the source $X \sim \mathcal{N}(0, \sigma^2)$ with the constant reconstruction $\hat{X} = 0$ has joint law $\mathcal{N}(0, \sigma^2) \otimes \delta_0$ and zero mutual information.
