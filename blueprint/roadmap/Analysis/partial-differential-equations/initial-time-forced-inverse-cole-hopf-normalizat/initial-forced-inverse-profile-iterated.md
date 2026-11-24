# Second spatial derivative of the forced inverse

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

If $u(t,\cdot)$ is $C^2$, then for arbitrary $q,\nu,a,x$,

$$\partial_x^2\Phi_q(t,x)=\left(\frac{u(t,x)^2}{4\nu^2}-\frac{u_x(t,x)}{2\nu}\right)\Phi_q(t,x).$$

The left side is the actual second iterated derivative. No temporal regularity is required, and total division includes $\nu=0$.
