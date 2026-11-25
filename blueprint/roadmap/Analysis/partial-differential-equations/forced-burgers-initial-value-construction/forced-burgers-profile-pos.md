# Strict positivity of the forced Burgers profile

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

At every $t\in[0,T]$ and $x\in\mathbb R$,

$$
\Phi(t,x)>0.
$$

No uniform positive lower bound on $g$ is required. In particular, exponential primitives that tend to zero at infinity are allowed. Initial and terminal times are included, also when $T=0$.
