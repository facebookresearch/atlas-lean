# Below-range inputs saturate to the least code

Let $k_{\min}, k_{\max}$ be integers and $\Delta, x \in \mathbb{R}$, and let the saturating code be $\max(k_{\min}, \min(k_{\max}, \operatorname{round}(x/\Delta)))$, with round taking the nearest integer (ties toward $+\infty$). If $\operatorname{round}(x/\Delta) < k_{\min}$, the code equals $k_{\min}$.

Division is total, with $x/0 = 0$, so for $\Delta = 0$ the rounded input is $\operatorname{round}(0) = 0$ and the code is $\max(k_{\min}, \min(k_{\max}, 0))$.
