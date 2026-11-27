# Rank threshold versus p-value threshold

Let $n \in \mathbb{N}$, $\alpha \in \mathbb{R}$ and $\omega \in \mathbb{R}^{n+1}$. The strict lower count is below $\lceil (1 - \alpha)(n + 1) \rceil$ (the ceiling being $0$ when $(1-\alpha)(n+1) \le 0$) if and only if $\alpha$ is below the [permutation p-value](permutation-pvalue-eval-last.md) of the test score:

$$L(\omega) < \lceil (1 - \alpha)(n + 1) \rceil \iff \alpha < \frac{n + 1 - L(\omega)}{n + 1}.$$

No restriction on $\alpha$ is needed.
