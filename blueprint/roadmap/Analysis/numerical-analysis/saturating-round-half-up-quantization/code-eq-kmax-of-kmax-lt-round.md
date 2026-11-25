# Above-range inputs saturate to the greatest code

Let $k_{\min} \le k_{\max}$ be integers and $\Delta, x \in \mathbb{R}$. If $\operatorname{round}(x/\Delta) > k_{\max}$ (nearest integer, ties toward $+\infty$), the saturating code $\max(k_{\min}, \min(k_{\max}, \operatorname{round}(x/\Delta)))$ equals $k_{\max}$.
