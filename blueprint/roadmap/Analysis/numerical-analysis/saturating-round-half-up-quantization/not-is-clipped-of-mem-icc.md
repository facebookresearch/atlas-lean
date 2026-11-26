# Inputs in the full-scale interval are not clipped

Let $\Delta > 0$ and integers $k_{\min}, k_{\max}$. Every $x \in [\Delta k_{\min}, \Delta k_{\max}]$ is unclipped: $k_{\min} \le \operatorname{round}(x/\Delta) \le k_{\max}$, with round taking the nearest integer (ties toward $+\infty$).
