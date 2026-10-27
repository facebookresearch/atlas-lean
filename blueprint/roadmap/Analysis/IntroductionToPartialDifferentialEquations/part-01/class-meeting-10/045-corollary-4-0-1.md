---
article_id: af_a82e73ad31876933b610fc87
declaration: theorem
origin: cited
lean: WaveEquation1D.dAlembert_halfline_corollary
---

# Corollary 4.0.1

Let $f \in C^{2}([0, \infty)), g \in C^{1}([0, \infty))$, and assume that $f(0)=g(0)=0$. Then the unique solution to the following $1+1$ dimensional initial + boundary value problem
$$-\partial_{t}^{2} u(t, x)+\partial_{x}^{2} u(t, x) =0, \quad (t, x) \in[0, \infty) \times(0, \infty),$$
$$u(t, 0) =0, \quad t \in[0, \infty),$$
$$u(0, x) =f(x), \quad x \in(0, \infty),$$
$$\partial_{t} u(0, x) =g(x), \quad x \in(0, \infty)$$
satisfies $u \in C^{2}([0, \infty) \times[0, \infty))$. Furthermore, it can be represented as
$$u(t, x)= \begin{cases}\frac{1}{2}(f(x+t)+f(x-t))+\frac{1}{2} \int_{z=|x-t|}^{z=x+t} g(z) d z, & \text{ if } 0 \leq t \leq x, \\ \frac{1}{2}(f(x+t)-f(t-x))+\frac{1}{2} \int_{z=|x-t|}^{z=x+t} g(z) d z, & \text{ if } 0 \leq x \leq t.\end{cases}$$

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 4.1 (d'Alembert's formula)](044-d-alembert-s-formula.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #10, Section on wave equation](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
