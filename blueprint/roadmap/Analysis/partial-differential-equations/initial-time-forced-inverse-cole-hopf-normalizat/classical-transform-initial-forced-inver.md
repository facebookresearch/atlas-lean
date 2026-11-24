# Recovery of velocity from the forced inverse

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

If $u(t,\cdot)$ is continuous and $\nu\ne0$, then for every anchor $a$ and point $x$,

$$-2\nu\frac{\partial_x\Phi_q(t,x)}{\Phi_q(t,x)}=u(t,x).$$

The potential and time dependence may be arbitrary. Positivity of the exponential permits division by the profile.
