# Quantization error bound in the full-scale interval

Let $\Delta > 0$ and integers $k_{\min}, k_{\max}$, and consider the saturating round-half-up quantizer $Q(x) = \Delta \cdot \max\big(k_{\min}, \min(k_{\max}, \operatorname{round}(x/\Delta))\big)$, where round takes the nearest integer with ties toward $+\infty$. For every $x \in [\Delta k_{\min}, \Delta k_{\max}]$, $|Q(x) - x| \le \Delta/2$.
