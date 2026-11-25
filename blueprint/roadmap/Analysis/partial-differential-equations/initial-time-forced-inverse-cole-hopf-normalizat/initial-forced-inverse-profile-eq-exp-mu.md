# Potential correction as a time-only factor

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

Let $\Phi_0$ denote the velocity-only initial inverse profile, obtained by omitting the last double integral from $N_q$. For arbitrary fields and parameters,

$$\Phi_q(t,x)=\exp\left(\int_0^t\int_a^{a+1}q(s,y)\,dy\,ds\right)\Phi_0(t,x).$$

The factor is positive and independent of $x$. No integrability or regularity hypothesis is imposed on this algebraic exponential identity.
