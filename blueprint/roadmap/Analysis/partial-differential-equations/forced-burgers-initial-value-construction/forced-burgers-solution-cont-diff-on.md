# Positive-time joint smoothness of forced Burgers

For a real initial velocity $u_0$ and anchor $a$, put

$$
g(x)=\exp\left(-\frac{1}{2\nu}\int_a^x u_0(y)\,dy\right),\qquad
\Phi(t,x)=\operatorname{potentialHeatSolution}(\nu,q,g)(t,x),\qquad
u_q(t,x)=-2\nu\frac{\partial_x\Phi(t,x)}{\Phi(t,x)}.
$$

Let $\nu>0$, let $u_0:\mathbb R\to\mathbb R$ be continuous and bounded, and let $q:\mathbb R^2\to\mathbb R$ be jointly $C^\infty$. For each integer $n\ge0$, assume there is a real $C_n$ such that

$$
\|D^n q(t,x)\|\le C_n\qquad(0\le t\le T,\ x\in\mathbb R).
$$

The bound is uniform on the closed strip; its constant may depend on the derivative order. No derivative or bounded primitive of $u_0$ is assumed.

The field $(t,x)\mapsto u_q(t,x)$ is jointly $C^\infty$ on $(0,T)\times\mathbb R$. No smoothness at the initial or terminal time is asserted. If $T\le0$, this open domain is empty.

Both the profile and its actual first spatial derivative are jointly smooth on this domain, and the denominator is strictly positive.
