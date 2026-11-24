# Uniform velocity estimate for forced Burgers

Let $\nu>0$ and $T\ge0$. Let $u_0:\mathbb R\to\mathbb R$ be continuous and let $q:\mathbb R^2\to\mathbb R$ be jointly $C^\infty$, with a bound for every derivative order uniform on the closed strip:

$$
\forall n\ge0\quad\exists C_n\in\mathbb R\quad
\forall(t,x)\in[0,T]\times\mathbb R,\qquad \|D^nq(t,x)\|\le C_n.
$$

For an arbitrary anchor $a$, let $\Phi$ be the potential-heat Volterra evolution of

$$
g(x)=\exp\left(-\frac{1}{2\nu}\int_a^x u_0(y)\,dy\right),
$$

and let $u(t,x)=-2\nu\,\partial_x\Phi(t,x)/\Phi(t,x)$ be its logarithmic-derivative field.

Assume $M,A\ge0$ satisfy

$$
|u_0(x)|\le M,\qquad |\partial_xq(t,x)|\le A
\qquad(0\le t\le T,\ x\in\mathbb R).
$$

Then, throughout the closed strip,

$$
|u(t,x)|\le M+2\nu At.
$$

This includes both endpoints and the zero horizon. There is no assumption that the velocity field is already bounded, that the initial primitive is bounded, or that the initial velocity is differentiable.

To prove the estimate, put $B(t)=M+2\nu At$. The potential-heat residual of $B\Phi$ is $2\nu A\Phi$, while that of $c\partial_x\Phi$ is $c\partial_xq\,\Phi$. For $c=\pm2\nu$, comparison applies because these residuals and the initial values are ordered. The required exponential growth is established for $\Phi$ and $\partial_x\Phi$. Strict positivity of $\Phi$ then permits division.

The comparison background is Nolen, [Partial Differential Equations and Diffusion Processes](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), section 2.8. The forcing convention $u_t+uu_x-\nu u_{xx}=-2\nu q_x$ is the Cole–Hopf identity in Gesztesy and Holden, [The Cole–Hopf and Miura transformations revisited](https://arxiv.org/abs/solv-int/9812025), Lemmas 3.1–3.2.
