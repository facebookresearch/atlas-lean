# Monotonicity, uniqueness and speed range of the line-supported front

**Statement.** Consider the dimensionless line-supported production problem $\partial_tu=\Delta u-u+\theta(u-\alpha)\delta(y)$ on $\mathbb R^2$ with $\alpha\in(0,1/2)$, its stationary state $s(y)=\frac12e^{-|y|}$, and its exact travelling front $u=w(x-vt,y)$ with speed $v=2\cot(2\pi\alpha)$. Then:

1. **Monotonicity.** For every fixed $y$, $w(\cdot,y)$ is decreasing on $\mathbb R$; for every fixed $x$, $w(x,\cdot)$ is decreasing on $(0,\infty)$ and increasing on $(-\infty,0)$.
2. **Connection.** For every $y$, $w(x,y)\to0$ as $x\to+\infty$ and $w(x,y)\to s(y)$ as $x\to-\infty$; the front joins the trivial state to the nonhomogeneous active state.
3. **Uniqueness.** Up to reflection $x\mapsto -x$ and translation in $x$, it is the only travelling physical solution whose trace on the line is below $\alpha$ on one side ($w(x,0)<\alpha$ for $x>x_1$) and above $\alpha$ on the other ($w(x,0)>\alpha$ for $x<x_2$).
4. **Speed range.** As $\alpha$ ranges over $(0,1/2)$, $v=2\cot(2\pi\alpha)$ takes every real value, decreasing in $\alpha$. The front is stationary exactly at $\alpha=1/4$; for $\alpha<1/4$ the active state invades ($v>0$), and for $\alpha>1/4$ it retreats ($v<0$).

## Expansion

These are the properties of monotone fronts in classical bistable reaction–diffusion equations: a unique speed, monotone profile, and a sign change of the speed at a balance value of the threshold (here $\alpha=1/4$, the analogue of equal-area). Monotonicity follows from positivity of the Green's function of $-\Delta-v\partial_x+1$ and the half-line structure of the source. Uniqueness uses temperedness: any solution with a single switching point on the line is the Green's-function response to a half-line source, and the threshold condition at the switching point pins the speed. In dimensional form, invasion along the edge requires $u_c<\frac{a}{4\sqrt{kD}}$, i.e. production strong enough relative to the bulk loss length $\sqrt{D/k}$.

## Depends on

- [Exact travelling front for line-supported piecewise-constant production](exact-travelling-front-for-line-supported-piecewise-constant-production.md)

## Sources

- A. S. Zadorin, "Exact travelling solution for a reaction-diffusion system with a piecewise constant production supported by a codimension-1 subspace" (2019), Results, Theorem 3. <https://doi.org/10.48550/arXiv.1906.00484>
