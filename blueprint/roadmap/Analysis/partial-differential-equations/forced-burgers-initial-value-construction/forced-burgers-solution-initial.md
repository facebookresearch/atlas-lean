# Exact recovery of the initial velocity

For a real initial velocity $u_0$ and anchor $a$, put

$$
g(x)=\exp\left(-\frac{1}{2\nu}\int_a^x u_0(y)\,dy\right),\qquad
\Phi(t,x)=\operatorname{potentialHeatSolution}(\nu,q,g)(t,x),\qquad
u_q(t,x)=-2\nu\frac{\partial_x\Phi(t,x)}{\Phi(t,x)}.
$$

If $u_0$ is continuous and $\nu\ne0$, then for every potential $q$, anchor $a$ and point $x$,

$$
u_q(0,x)=u_0(x).
$$

This initial identity needs neither boundedness of $u_0$ or its primitive nor regularity of $q$. It follows by differentiating the exponential primitive and using its strict positivity.
