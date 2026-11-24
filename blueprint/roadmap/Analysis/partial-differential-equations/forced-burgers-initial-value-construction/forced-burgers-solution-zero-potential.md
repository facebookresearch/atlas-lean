# Zero-potential compatibility of forced Burgers

For a real initial velocity $u_0$ and anchor $a$, put

$$
g(x)=\exp\left(-\frac{1}{2\nu}\int_a^x u_0(y)\,dy\right),\qquad
\Phi(t,x)=\operatorname{potentialHeatSolution}(\nu,q,g)(t,x),\qquad
u_q(t,x)=-2\nu\frac{\partial_x\Phi(t,x)}{\Phi(t,x)}.
$$

For the zero potential and arbitrary real parameters and data,

$$
u_{q=0}(t,x)=\operatorname{burgersSolution}(\nu,u_0,a,t,x).
$$

Thus the field is the logarithmic derivative of the free heat evolution of $g$. This algebraic compatibility holds for all real times and viscosities; it makes no extra evolution assertion outside the usual positive-viscosity domain.
