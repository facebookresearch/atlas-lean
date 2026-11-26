# Spatial derivative of the heat solution for exponentially growing data

Let $\Phi(t, x) = (4\pi t)^{-1/2} e^{-x^2/(4t)}$ be the heat kernel on $\mathbb{R}$, and for $f : \mathbb{R} \to \mathbb{R}$ let $u(t, x) = \int \Phi(t, x - y) f(y)\, dy$ for $t > 0$ (and $u(t, x) = f(x)$ for $t \le 0$). Let $f$ be almost everywhere strongly measurable with at most exponential growth ($|f(x)| \le M e^{c|x|}$ for some $M, c \ge 0$), and let $M_n(a, b) = \int y^n e^{-a y^2 + b y} f(y)\, dy$. For $t > 0$ and every $x$, $u(t, \cdot)$ is differentiable at $x$ with

$$\partial_x u(t, x) = -\frac{x}{2t}\, u(t, x) + \frac{\Phi(t, x)}{2t}\, M_1\Big(\frac{1}{4t}, \frac{x}{2t}\Big).$$
