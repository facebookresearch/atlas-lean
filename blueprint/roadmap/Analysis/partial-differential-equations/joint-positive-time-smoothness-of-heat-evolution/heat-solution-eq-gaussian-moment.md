# The heat solution as a Gaussian moment

Let $\Phi(t, x) = (4\pi t)^{-1/2} e^{-x^2/(4t)}$ be the heat kernel on $\mathbb{R}$, and for $f : \mathbb{R} \to \mathbb{R}$ let $u(t, x) = \int \Phi(t, x - y) f(y)\, dy$ for $t > 0$ (and $u(t, x) = f(x)$ for $t \le 0$). With the Gaussian moments $M_n(a, b) = \int y^n e^{-a y^2 + b y} f(y)\, dy$, for every $f$, $t > 0$ and $x$,

$$u(t, x) = (4\pi t)^{-1/2} e^{-x^2/(4t)}\, M_0\Big(\frac{1}{4t}, \frac{x}{2t}\Big).$$

Integrals here are Bochner integrals, under the convention that the integral of a non-integrable function is $0$; the statement holds for every function under that convention, and has its classical meaning when the integrands are integrable.
