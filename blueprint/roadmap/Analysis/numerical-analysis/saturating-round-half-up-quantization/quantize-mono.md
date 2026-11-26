# The quantizer is monotone

For $\Delta > 0$ and integers $k_{\min}, k_{\max}$, the saturating round-half-up quantizer $Q(x) = \Delta \cdot \max\big(k_{\min}, \min(k_{\max}, \operatorname{round}(x/\Delta))\big)$, where round takes the nearest integer with ties toward $+\infty$ is monotone.
