# Forced Burgers equation for the constructed field

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

For every $0<t<T$ and $x\in\mathbb R$, the ordinary derivatives satisfy

$$
\partial_t u_q(t,x)+u_q(t,x)\partial_xu_q(t,x)
-\nu\partial_{xx}u_q(t,x)=-2\nu\partial_xq(t,x).
$$

The forcing has the displayed sign and viscosity factor. No endpoint time derivative is asserted. Applying the local Cole–Hopf identity to the positive potential-heat field gives this equation; see Gesztesy and Holden, [The Cole–Hopf and Miura transformations revisited](https://arxiv.org/abs/solv-int/9812025), Lemmas 3.1–3.2 and Theorem 3.3(ii).
