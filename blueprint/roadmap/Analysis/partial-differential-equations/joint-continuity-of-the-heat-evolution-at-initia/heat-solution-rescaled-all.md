# Heat evolution as a rescaled Gaussian integral

For every $f : \mathbb{R} \to \mathbb{R}$ and all real $t, x$, the heat evolution of $f$ satisfies $u(t, x) = \int_{\mathbb{R}} G_1(y)\, f(x - \sqrt{t}\, y)\,dy$, where $G_1(y) = (4\pi)^{-1/2} e^{-y^2/4}$ is the heat kernel at time $1$ and $\sqrt{t} = 0$ for $t \le 0$, where $u(t, x) = f(x)$.

Integrals here are Bochner integrals, under the convention that the integral of a non-integrable function is $0$; that is what makes the statement hold for every $f$. For instance, at $t = 1$, $x = 0$ and $f(y) = e^{y^2/4}$ the integrand is a positive constant, so the integral is $0$ by convention, not a divergent classical integral.
