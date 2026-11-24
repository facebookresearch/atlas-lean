# Boundedness on a finite closed time strip

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

If the continuous initial velocity is bounded, then there exists a real $C$ such that

$$
|u(t,x)|\le C\qquad(0\le t\le T,\ x\in\mathbb R).
$$

This is boundedness of the specified logarithmic-derivative field, derived from the data. A bound on the first joint derivative of $q$ supplies a bound $A$ for $|q_x|$. Given a nonnegative initial bound $M$, the velocity estimate permits the choice $C=M+2\nu AT$.

The conclusion includes $T=0$. No derivative of $u_0$, bound on its primitive, or prior velocity bound is assumed.
