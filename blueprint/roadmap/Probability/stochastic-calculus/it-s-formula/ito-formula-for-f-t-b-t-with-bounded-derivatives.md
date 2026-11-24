# Itô's formula for $f(t,B_t)$ with bounded derivatives

Let $B$ be a real Brownian motion under $\mathbb P$, adapted to a filtration $(\mathcal F_t)$, jointly measurable in $(t,\omega)$, with increments $B_t-B_s$ ($s\le t$) independent of $\mathcal F_s$, as in [Itô's formula](ito-formula.md). Let $f:[0,\infty)\times\mathbb R\to\mathbb R$ be continuously differentiable in $t$ and twice continuously differentiable in $x$, with $f$, $\partial_tf$, $\partial_xf$ and $\partial_{xx}f$ bounded and continuous. Then for every $t\ge0$, almost surely,

$$f(t,B_t)=f(0,B_0)+\int_0^t\Bigl(\partial_tf+\frac12\partial_{xx}f\Bigr)(s,B_s)\,ds+\int_0^t\partial_xf(s,B_s)\,dB_s,$$

where the stochastic integral is the [$L^2$ Itô integral](../it-integral/ito-integral-2.md) and the time integral is pathwise. When $f$ does not depend on $t$ this is [Itô's formula](ito-formula.md).

## Depends on

- [Itô's formula](ito-formula.md)
- [Itô integral process](../it-integral/ito-integral-2.md)

## Proof depends on

- [Density of elementary integrands](../it-integral/is-ito-approximable-of-is-progressive.md)

## Expansion

A full proof page must establish the following.

- Telescoping over a partition of $[0,t]$ and splitting each increment as $[f(t_{k+1},B_{t_{k+1}})-f(t_k,B_{t_{k+1}})]+[f(t_k,B_{t_{k+1}})-f(t_k,B_{t_k})]$; the first bracket gives $\int\partial_tf\,ds$ by the mean value theorem and uniform continuity, the second is handled as in the time-independent formula, with left-point integrands $\partial_xf(t_k,B_{t_k})$ that are elementary and progressively measurable and converge to $\partial_xf(s,B_s)$ in $L^2(ds\otimes d\mathbb P)$.
- An example: for $\theta\in\mathbb R$, $g(t,x)=e^{\theta x-\theta^2t/2}$ is unbounded, so the formula applies to $g$ only after truncation, for instance to $g(t,x)\chi(x)$ with a smooth cutoff $\chi$ equal to $1$ on $[-R,R]$; up to the exit time of $B$ from $(-R,R)$ this recovers $g(t,B_t)=1+\int_0^t\theta g(s,B_s)\,dB_s$, the exponential martingale.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer (1991), <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, Itô's rule (statement and proof).
