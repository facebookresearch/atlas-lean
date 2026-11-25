# Joint initial trace of forced Burgers

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

For $T\ge0$ and each $x\in\mathbb R$,

$$
\lim_{\substack{(s,y)\to(0,x)\\(s,y)\in[0,T]\times\mathbb R}}u_q(s,y)=u_0(x).
$$

Both coordinates may vary in this limit. The statement includes the zero horizon, where the approach takes place inside $\{0\}\times\mathbb R$.
