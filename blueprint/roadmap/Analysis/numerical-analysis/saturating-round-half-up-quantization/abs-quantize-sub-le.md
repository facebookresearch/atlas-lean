# Quantization error bound for every input

Let $\Delta > 0$ and integers $k_{\min} \le k_{\max}$, and consider the saturating round-half-up quantizer $Q(x) = \Delta \cdot \max\big(k_{\min}, \min(k_{\max}, \operatorname{round}(x/\Delta))\big)$, where round takes the nearest integer with ties toward $+\infty$. For every $x \in \mathbb{R}$,

$$|Q(x) - x| \le |x - \pi(x)| + \frac{\Delta}{2},$$

where $\pi$ is the projection of $\mathbb{R}$ onto the full-scale interval $[\Delta k_{\min}, \Delta k_{\max}]$.
