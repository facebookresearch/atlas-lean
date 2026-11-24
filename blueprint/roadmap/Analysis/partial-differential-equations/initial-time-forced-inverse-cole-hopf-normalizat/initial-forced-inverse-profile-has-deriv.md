# Spatial derivative of the forced inverse

For real fields $u(t,x)$ and $q(t,x)$, an anchor $a$, and real $\nu$, write

$$
M_a(t)=\int_a^{a+1}(a+1-y)u(t,y)\,dy,\qquad
R_a(t)=\frac{1}{4\nu}\int_a^{a+1}u(t,y)^2\,dy-\frac{u(t,a+1)-u(t,a)}2,
$$

$$
N_q(t)=\frac{M_a(t)-M_a(0)}{2\nu}+\int_0^t R_a(s)\,ds
       +\int_0^t\int_a^{a+1}q(s,y)\,dy\,ds,\qquad
\Phi_q(t,x)=\exp\left(N_q(t)-\frac{1}{2\nu}\int_a^x u(t,y)\,dy\right).
$$

These expressions use oriented integrals and total real division, so division by zero has value zero. No regularity is implicit in the notation.

Fix a time $t$ and suppose only that $u(t,\cdot)$ is continuous. For arbitrary potential $q$, real $\nu$ and anchor $a$, the ordinary spatial derivative exists at every $x$ and satisfies

$$\partial_x\Phi_q(t,x)=-\frac{u(t,x)}{2\nu}\Phi_q(t,x).$$

No time regularity or PDE hypothesis is used; $\nu=0$ is included with total division.
