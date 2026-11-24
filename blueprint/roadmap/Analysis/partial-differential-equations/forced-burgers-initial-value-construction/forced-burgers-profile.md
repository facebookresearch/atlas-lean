# Potential-heat profile for an initial velocity

For a real initial velocity $u_0$ and anchor $a$, put

$$
g(x)=\exp\left(-\frac{1}{2\nu}\int_a^x u_0(y)\,dy\right),\qquad
\Phi(t,x)=\operatorname{potentialHeatSolution}(\nu,q,g)(t,x),\qquad
u_q(t,x)=-2\nu\frac{\partial_x\Phi(t,x)}{\Phi(t,x)}.
$$

The profile is defined by the Volterra series: with $P_s$ the free heat operator, set $\Phi_0(t)=P_{\nu t}g$ and

$$
\Phi_{k+1}(t,x)=\int_0^t P_{\nu(t-s)}\bigl(q(s,\cdot)\Phi_k(s,\cdot)\bigr)(x)\,ds,
\qquad \Phi=\sum_{k=0}^\infty\Phi_k.
$$

This definition allows arbitrary real parameters and data. Convergence, positivity and evolution require additional hypotheses, as in the linked results.
