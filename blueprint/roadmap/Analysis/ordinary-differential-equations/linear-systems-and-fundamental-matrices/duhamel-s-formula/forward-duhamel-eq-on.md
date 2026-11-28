# Forward uniqueness of the Duhamel solution

Let $E$ be a real Banach space, $A : E \to E$ a bounded linear operator, $b : \mathbb{R} \to E$ continuous on $[0, \infty)$ and $x_0 \in E$. Let $y : \mathbb{R} \to E$ be continuous on $[0, \infty)$ with $y(0) = x_0$ and, at every $t \ge 0$, right derivative $A\,y(t) + b(t)$ (derivative within $[t, \infty)$). Then for every $t \ge 0$,

$$y(t) = e^{tA}x_0 + \int_0^t e^{(t - s)A}\,b(s)\,ds.$$
