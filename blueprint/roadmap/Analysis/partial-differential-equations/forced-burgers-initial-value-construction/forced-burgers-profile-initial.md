# Initial potential-heat profile

For a real initial velocity $u_0$ and anchor $a$, put

$$
g(x)=\exp\left(-\frac{1}{2\nu}\int_a^x u_0(y)\,dy\right),\qquad
\Phi(t,x)=\operatorname{potentialHeatSolution}(\nu,q,g)(t,x),\qquad
u_q(t,x)=-2\nu\frac{\partial_x\Phi(t,x)}{\Phi(t,x)}.
$$

For every real $\nu,a,x$, every $q$ and every $u_0$,

$$
\Phi(0,x)=g(x).
$$

No continuity, growth or positivity assumption is needed for this initial-time identity.
