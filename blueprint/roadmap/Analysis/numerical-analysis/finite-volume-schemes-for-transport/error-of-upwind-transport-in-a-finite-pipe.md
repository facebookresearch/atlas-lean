# Error of upwind transport in a finite pipe

Let $\ell,T>0$, $N\ge1$, $\Delta x=\ell/N>0$ and $\Delta t>0$. Set $t_n=n\Delta t$,
$x_i=(i+1)\Delta x$ for $i=0,\ldots,N-1$, and $x_{-1}=0$. These are nodal values, not cell averages.
Let $u$ be a $C^2$ solution of $u_t + a u_x = 0$ with $a > 0$ on $[0, \ell] \times [0, T]$, with $\lvert u_{tt}\rvert \le B_{tt}$
and $\lvert u_{xx}\rvert \le B_{xx}$, and run the upwind scheme $u_i^{n+1} = (1 - \nu) u_i^n + \nu u_{i-1}^n$ on a uniform grid with
$0 < \nu = a\Delta t/\Delta x \le 1$, exact inflow values $u_{-1}^n = u(x_{-1}, t_n)=u(0,t_n)$ and initial values within $\varepsilon_0\ge0$ of the
exact ones. Then for $n\Delta t \le T$ the maximum error satisfies

$$\max_i \lvert u_i^n - u(x_i, t_n)\rvert \le \varepsilon_0 + \frac{T}{2}\bigl(\Delta t\,B_{tt} + a\,\Delta x\,B_{xx}\bigr).$$

The scheme's coefficients are nonnegative and sum to one, so the error grows by at most the local truncation error,
$\frac{\Delta t}{2}(\Delta t\,B_{tt} + a\,\Delta x\,B_{xx})$, per step, by Taylor's theorem. Splitting, roundoff and the general Lax
equivalence theorem are outside this result. Matching physical length, time and concentration scales to this nodal theorem is
a separate step: the bound above does not by itself establish that correspondence, and error results for periodic grids do not apply to this inflow boundary.

## Depends on

## Proof depends on

## Sources

- *Numerical Methods I* lecture notes, University of Münster, Chapter 2 (advection equation), Section 2.2, upwind schemes and the CFL condition (2.7), <https://www.uni-muenster.de/imperia/md/content/physik_tp/lectures/ws2016-2017/num_methods_i/advection.pdf>.
- L. R. Hellevik, *Numerical Methods for Engineers*, NTNU, Section 7.3, criterion for positive coefficients, Equations 7.18–7.21, <https://leifh.folk.ntnu.no/teaching/tkt4140/>.
