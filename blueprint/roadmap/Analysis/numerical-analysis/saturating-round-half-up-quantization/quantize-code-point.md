# Code points are fixed by the quantizer

Let $\Delta > 0$ and integers $k_{\min} \le k \le k_{\max}$. The code point $\Delta k$ is a fixed point of the saturating round-half-up quantizer $Q(x) = \Delta \cdot \max\big(k_{\min}, \min(k_{\max}, \operatorname{round}(x/\Delta))\big)$, where round takes the nearest integer with ties toward $+\infty$: $Q(\Delta k) = \Delta k$.
