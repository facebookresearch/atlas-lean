# Gronwall inequality in integral form

Let $T>0$ and $a,b\ge0$, and let $u:[0,T]\to[0,\infty)$ be bounded and Lebesgue measurable. If

$$u(t)\le a+b\int_0^t u(s)\,ds\qquad\text{for every }t\in[0,T],$$

then

$$u(t)\le a\,e^{bt}\qquad\text{for every }t\in[0,T].$$

The differential form is the case $a=u(0)$: if $u:[0,T]\to[0,\infty)$ is continuously differentiable and $u'(t)\le b\,u(t)$ for every $t\in[0,T]$, then $u(t)=u(0)+\int_0^tu'(s)\,ds\le u(0)+b\int_0^tu(s)\,ds$, hence $u(t)\le u(0)\,e^{bt}$.

## Proof depends on

- [Monotonicity of the integral of integrable functions](../../../MeasureTheory/integration/nonnegative-lebesgue-integral/lebesgue-integral/integral-mono.md)
- [Power series of the real exponential function](../../special-functions/elementary-transcendental-functions/real-exponential-power-series.md)

## Expansion

A proof iterates the hypothesis. By induction on $n\ge1$,

$$u(t)\le a\sum_{k=0}^{n-1}\frac{(bt)^k}{k!}+\frac{(bt)^n}{n!}\,\sup_{[0,T]}u\qquad(t\in[0,T]),$$

since substituting the bound into $\int_0^t u$ and integrating the polynomial terms raises each power by one. Boundedness of $u$ makes the remainder tend to $0$ as $n\to\infty$, and the partial sums tend to $e^{bt}$. Measurability is needed only so that $\int_0^tu$ is defined. The inequality is the uniqueness step of [Global existence and uniqueness for globally Lipschitz ODEs](../maximal-solutions-and-global-existence/ode-global-exists-of-global-lipschitz.md) and of pathwise uniqueness arguments for stochastic differential equations, where it is applied to $u(t)=\mathbb E\,|X_t-Y_t|$ or $\mathbb E\,|X_t-Y_t|^2$.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer, 1991, <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, the Gronwall lemma used for uniqueness of stochastic differential equations.
