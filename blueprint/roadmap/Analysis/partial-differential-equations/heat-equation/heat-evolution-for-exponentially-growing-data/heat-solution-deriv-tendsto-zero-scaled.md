# Initial trace of the spatial derivative for exponentially growing data

Let $\Phi(t, x) = (4\pi t)^{-1/2} e^{-x^2/(4t)}$ be the heat kernel on $\mathbb{R}$, and for $f : \mathbb{R} \to \mathbb{R}$ let $u(t, x) = \int \Phi(t, x - y) f(y)\, dy$ for $t > 0$ (and $u(t, x) = f(x)$ for $t \le 0$). Let $f$ be $C^1$ with $f$ and $f'$ of at most exponential growth, and $\nu > 0$. For every $x$, $\partial_x u(\nu t, x) \to f'(x)$ as $t \to 0^+$.
