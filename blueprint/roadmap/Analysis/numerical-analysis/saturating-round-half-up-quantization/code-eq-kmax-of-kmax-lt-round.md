# Above-range inputs saturate to the greatest code

Let $k_{\min} \le k_{\max}$ be integers and $\Delta, x \in \mathbb{R}$. If $\operatorname{round}(x/\Delta) > k_{\max}$ (nearest integer, ties toward $+\infty$), the saturating code $\max(k_{\min}, \min(k_{\max}, \operatorname{round}(x/\Delta)))$ equals $k_{\max}$.

Division is total, with $x/0 = 0$, so for $\Delta = 0$ the rounded input is $\operatorname{round}(0) = 0$ and the code is $\max(k_{\min}, \min(k_{\max}, 0))$.
