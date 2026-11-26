# Critical upstream protection-zone length for persistence under toxicant exposure

**Model.** A population $u(x,t)$ in a river $(0,L)$ with diffusion $d_1>0$, advection $a_1>0$ and intrinsic growth $r>0$ is harmed by a toxicant $w(x,t)$ that is present only outside an upstream protection zone $(0,x_1]$:
$$\begin{cases}
u_t = d_1 u_{xx} - a_1 u_x + u\big(r - u - m\,\chi_{(x_1,L]}\,w\big), & x\in(0,L),\\
w_t = d_2 w_{xx} - a_2 w_x + h - q w - p u w, & x\in(x_1,L),
\end{cases}$$
with zero-flux (Danckwerts) conditions $d_1u_x - a_1u = 0$ at $x=0$, $d_2w_x - a_2w=0$ at $x=x_1$, and $u_x = w_x = 0$ at $x=L$. Here $m$ is the toxicant effect on growth, $h$ the toxicant input, $q$ its decay and $p$ its uptake by the population. The system has a unique toxicant-only steady state $(0,\tilde w)$. Define, for $0<a_1<\sqrt{4d_1r}$,
$$L^{*} = 2d_1\,\frac{\pi - \arctan\big(\sqrt{4d_1r-a_1^2}/a_1\big)}{\sqrt{4d_1r-a_1^2}},$$
and $L_1^{*}<L^{*}$ the critical domain length of the toxicant-free logistic problem.

**Theorem.**

1. If $a_1 \ge \sqrt{4d_1r}$, or $a_1<\sqrt{4d_1r}$ and $L<L_1^{*}$, then $(0,\tilde w)$ is globally asymptotically stable: the population dies out.
2. Let $0<a_1<\sqrt{4d_1r}$ and $L>L_1^{*}$. Let $\lambda_1(V)$ denote the principal eigenvalue of $d_1\phi''-a_1\phi'+V\phi=\lambda\phi$ on $(0,L)$ with the boundary conditions above (positive means the population grows when rare), and let $\lambda_1^{D}(x_1)=\lim_{\xi\to\infty}\lambda_1(r-\xi\chi_{(x_1,L]})$, the eigenvalue of the protection zone $(0,x_1)$ with a Dirichlet condition at $x_1$. Then $\lambda_1^{D}(x_1)$ is negative, zero or positive according as $x_1<L^{*}$, $x_1=L^{*}$ or $x_1>L^{*}$. If $x_1 \ge L^{*}$ (large protection zone), $(0,\tilde w)$ is unstable for every $m,q,h>0$, so the population persists regardless of toxicant parameters. If $x_1<L^{*}$, there are thresholds $m^{*}(x_1)$, $h^{*}(x_1)$ (strictly increasing in $x_1$) and $q^{*}(x_1)$ (strictly decreasing) such that $(0,\tilde w)$ is linearly stable iff $m>m^{*}$, iff $h>h^{*}$, iff $q<q^{*}$ (each with the other parameters fixed), and unstable under the reverse strict inequality.

## Expansion

Instability of $(0,\tilde w)$ is decided by the sign of $\lambda_1(r-m\chi_{(x_1,L]}\tilde w)$, which decreases in $m$ and is bounded below by $\lambda_1^{D}(x_1)$, its limit as the toxicant penalty becomes infinite. For the protection-zone problem the substitution $\phi = e^{a_1x/(2d_1)}\psi$ turns it into a constant-coefficient problem whose first eigenfunction is a sine with frequency $\sqrt{4d_1r-a_1^2}/(2d_1)$, and matching the boundary conditions gives $L^{*}$. Monotone dependence on $m,h,q$ follows from monotonicity of $\tilde w$ and of the principal eigenvalue in the potential.

## Sources

- J. Gao, X. Wang, G. Zhang, "Effect of protection zone on the dynamics of a diffusion-advection population-toxicant model", arXiv:2508.01246, Section 2, Theorem 2.1 and Proposition 2. <https://doi.org/10.48550/arXiv.2508.01246>
