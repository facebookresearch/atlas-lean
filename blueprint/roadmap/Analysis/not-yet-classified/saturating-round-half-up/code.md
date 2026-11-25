# Saturating round-half-up code

For a step $\Delta \in \mathbb{R}$, integer code endpoints $k_{\min}$ and $k_{\max}$, and input $x \in \mathbb{R}$, the saturating code is

$$\operatorname{code}(x) = \max\bigl(k_{\min},\ \min(k_{\max},\ \operatorname{round}(x/\Delta))\bigr),$$

where $\operatorname{round}(y) = \lfloor y + 1/2 \rfloor$ rounds to the nearest integer with ties toward $+\infty$. For $\Delta = 0$ the formula takes the convention $x/0 = 0$, giving $\max(k_{\min}, \min(k_{\max}, 0))$.
