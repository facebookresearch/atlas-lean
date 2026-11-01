---
article_id: af_2cc33c54aa19bf73b8c1eebb
declaration: theorem
origin: cited
statement: formalized
lean: WaveEquation3D.sphericalAverage_solves_1d_wave
---

# Proposition 1.0.1 (Spherical averages)

Let $u(t, x) \in C^{2}([0, \infty) \times \mathbb{R}^{3})$ be a solution to the $1+3$ dimensional global Cauchy problem
$$-\partial_{t}^{2} u(t, x)+\Delta u(t, x) =0, \quad (t, x) \in[0, \infty) \times \mathbb{R}^{3},$$
$$u(0, x) =f(x), \quad x \in \mathbb{R}^{3},$$
$$\partial_{t} u(0, x) =g(x), \quad x \in \mathbb{R}^{3}.$$
For each $r>0$, define the spherically averaged quantities
$$U(t, r ; x) \coloneqq \frac{1}{4 \pi r^{2}} \int_{\partial B_{r}(x)} u(t, \sigma) d \sigma=\frac{1}{4 \pi} \int_{\omega \in \partial B_{1}(0)} u(t, x+r \omega) d \omega,$$
$$F(r ; x) \coloneqq \frac{1}{4 \pi r^{2}} \int_{\partial B_{r}(x)} f(\sigma) d \sigma,$$
$$G(r ; x) \coloneqq \frac{1}{4 \pi r^{2}} \int_{\partial B_{r}(x)} g(\sigma) d \sigma,$$
and their related modifications
$$\widetilde{U}(t, r ; x) \coloneqq r U(t, r ; x), \quad \widetilde{F}(r ; x) \coloneqq r F(r ; x), \quad \widetilde{G}(r ; x) \coloneqq r G(r ; x).$$
Then $\widetilde{U}(t, r ; x) \in C^{2}([0, \infty) \times[0, \infty))$ is a solution to the following initial + boundary-value problem for the one-dimensional wave equation:
$$-\partial_{t}^{2} \widetilde{U}(t, r ; x)+\partial_{r}^{2} \widetilde{U}(t, r ; x) =0, \quad (t, r) \in[0, \infty) \times[0, \infty),$$
$$\widetilde{U}(t, 0 ; x) =0, \quad t \in[0, \infty),$$
$$\widetilde{U}(0, r ; x) =\widetilde{F}(r ; x), \quad r \in(0, \infty),$$
$$\partial_{t} \widetilde{U}(0, r ; x) =\widetilde{G}(r ; x), \quad r \in(0, \infty).$$
Furthermore,
$$\lim_{r \rightarrow 0} U(t, r ; x)=u(t, x).$$

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 7.1 (Divergence Theorem)](../class-meeting-1/011-divergence-theorem.md)
- [Proposition 1.1.1 (Differentiating under the integral)](../section-1/022-differentiating-under-the-integral.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #11, Section 1](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
