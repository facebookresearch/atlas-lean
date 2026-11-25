# Potential-heat equation for the forced inverse

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

Fix $t\in(0,T)$ and $\nu\ne0$. Assume $u,q$ are jointly continuous on $[0,T]\times\mathbb R$. At every point of $(0,T)\times\mathbb R$, the ordinary time derivative $u_t$ exists, and this actual derivative is jointly continuous there. Assume the current spatial slice $u(t,\cdot)$ is $C^2$, the current slice $q(t,\cdot)$ is differentiable, and, for every $y\in\mathbb R$,

$$
u_t(t,y)+u(t,y)u_x(t,y)=\nu u_{xx}(t,y)-2\nu q_x(t,y).
$$

These hypotheses do not require mixed velocity derivatives, a second time derivative, or a bound on $u_x$ near initial time. Define

$$
\rho_\nu(u;x,t)=\frac{u(t,x)^2}{4\nu}-\frac{u_x(t,x)}2.
$$

For every anchor $a$ and point $x$, the ordinary time derivative exists at the chosen interior time and satisfies

$$\partial_t\Phi_q(t,x)=\nu\partial_x^2\Phi_q(t,x)+q(t,x)\Phi_q(t,x).$$

Both derivatives are actual derivatives of the defined profile. No mild representation, assumed heat solution, or normalization derivative is supplied as a premise.
