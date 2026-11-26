# Periodic upwind–diffusion scheme

Let $\ell,T,\Delta x,\Delta t>0$ and $t_n=n\Delta t$. On a periodic grid of $N \ge 2$ nodes $x_j = j\,\Delta x$ with $N\Delta x = \ell$, consider $u_t + a u_x = D u_{xx}$ with $a \ge 0$ and
$D \ge 0$ and the explicit scheme

$$u_j^{n+1} = (1 - \nu - 2\mu)\,u_j^n + (\nu + \mu)\,u_{j-1}^n + \mu\,u_{j+1}^n, \qquad \nu = \frac{a\Delta t}{\Delta x},\quad
\mu = \frac{D\Delta t}{\Delta x^2},$$

with indices modulo $N$. Here $\nu,\mu\ge0$. If $\nu + 2\mu \le 1$, the coefficients are nonnegative and sum to one, so the scheme keeps nonnegative data
nonnegative, keeps every $u_j^{n+1}$ between the minimum and maximum of the $u^n$, and conserves $\sum_j u_j^n$. If $u$ is a
classical $\ell$-periodic solution, $C^2$ in time and $C^4$ in space on the periodic cylinder (with the indicated derivatives
continuous up to the time endpoints), with $\lvert u_{tt}\rvert \le B_{tt}$, $\lvert u_{xx}\rvert \le B_{xx}$ and $\lvert u_{xxxx}\rvert \le B_4$ on
$[0, T]$, and the initial values are within $\varepsilon_0\ge0$ of $u(x_j, 0)$, then for $n\Delta t \le T$

$$\max_j \bigl\lvert u_j^n - u(x_j, t_n)\bigr\rvert \le \varepsilon_0 + \frac{T}{2}\Bigl(\Delta t\,B_{tt} + a\,\Delta x\,B_{xx}
+ \frac{D\,\Delta x^2}{6}\,B_4\Bigr),$$

because the local truncation error is at most $\tfrac{\Delta t}{2}$ times the bracket, by Taylor's theorem, and the error grows by at most
that per step. The values are nodal samples; for $D = 0$ this is the periodic upwind step.

## Depends on

## Proof depends on

## Sources

- L. R. Hellevik, *Numerical Methods for Engineers*, NTNU, Section 7.3, criterion for positive coefficients, Equations 7.18–7.21, <https://leifh.folk.ntnu.no/teaching/tkt4140/>.
- *Numerical Methods I* lecture notes, University of Münster, Chapter 2 (advection equation), Section 2.2, upwind schemes and the CFL condition (2.7), <https://www.uni-muenster.de/imperia/md/content/physik_tp/lectures/ws2016-2017/num_methods_i/advection.pdf>.
