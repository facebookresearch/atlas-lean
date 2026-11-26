# Quantization error bound for signed codes

Let $\Delta > 0$ and $w \ge 1$, and use signed $w$-bit codes $k_{\min} = -2^{w-1}$, $k_{\max} = 2^{w-1} - 1$ in the saturating round-half-up quantizer $Q(x) = \Delta \cdot \max\big(k_{\min}, \min(k_{\max}, \operatorname{round}(x/\Delta))\big)$, where round takes the nearest integer with ties toward $+\infty$. For every $x \in [\Delta k_{\min}, \Delta k_{\max}]$, $|Q(x) - x| \le \Delta/2$.
