# The saturating code lies in the code range

Let $k_{\min}, k_{\max}$ be integers and $\Delta, x \in \mathbb{R}$, and let the saturating code be $\max(k_{\min}, \min(k_{\max}, \operatorname{round}(x/\Delta)))$, with round taking the nearest integer (ties toward $+\infty$). If $k_{\min} \le k_{\max}$, the code lies in $[k_{\min}, k_{\max}]$ for every $\Delta$ and $x$.

Division is total, with $x/0 = 0$, so for $\Delta = 0$ the rounded input is $\operatorname{round}(0) = 0$ and the code is $\max(k_{\min}, \min(k_{\max}, 0))$.
