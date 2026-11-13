# Ramanujan's master theorem

Let $a$ and $b$ be real numbers with $0 < a < b$, and let
$s$ be a complex number with $a < \operatorname{Re} s < b$. Let $\varphi$ be a function from
$\mathbb{C}$ to $\mathbb{C}$ that is analytic on the half-plane $\operatorname{Re} z > -b$, and
suppose there are real constants $C > 0$ and $P < \pi$ such that
$|\varphi(u + iv)| \le C e^{P|v|}$ for all real $u$ and $v$ with $u > -b$. Let $F$ be a function
from $\mathbb{R}$ to $\mathbb{C}$ such that for every real $x > 0$ the series
$\sum_{k=0}^{\infty} \varphi(k)\,(-x)^k / k!$ converges unconditionally to $F(x)$, and suppose
that $x \mapsto x^{s-1} F(x)$ is Lebesgue integrable on $(0, \infty)$, where
$x^{s-1} = e^{(s-1)\log x}$. Then

$$\int_0^\infty x^{s-1} F(x)\,dx = \Gamma(s)\,\varphi(-s).$$

This is a specialization of the theorem: the growth bound on $\varphi$ is uniform in
$\operatorname{Re} z$, and integrability of $x^{s-1} F(x)$ is assumed rather than derived.

## Sources

- https://en.wikipedia.org/wiki/Ramanujan%27s_master_theorem (Raw: `int_0^infty x^{s-1} sum_k phi(k)(-x)^k/k! dx = Gamma(s) phi(-s)`.)
