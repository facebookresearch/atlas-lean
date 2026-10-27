---
article_id: af_8dc604e514e536c94bfc4ebe
declaration: theorem
origin: cited
lean: WaveEquation3D.kirchhoff_formula
---

# Theorem 1.1 (Kirchhoff's formula)

Assume that $f \in C^{3}(\mathbb{R}^{3})$ and $g \in C^{2}(\mathbb{R}^{3})$. Then the unique solution $u(t, x)$ to the global Cauchy problem
$$-\partial_{t}^{2} u(t, x)+\Delta u(t, x) =0, \quad (t, x) \in[0, \infty) \times \mathbb{R}^{3},$$
$$u(0, x) =f(x), \quad x \in \mathbb{R}^{3},$$
$$\partial_{t} u(0, x) =g(x), \quad x \in \mathbb{R}^{3}$$
in $1+3$ dimensions satisfies $u \in C^{2}([0, \infty) \times \mathbb{R}^{3})$ and can be represented as follows:
$$u(t, x)=\frac{1}{4 \pi t^{2}} \int_{\partial B_{t}(x)} f(\sigma) d \sigma+\frac{1}{4 \pi t} \int_{\partial B_{t}(x)} \nabla_{\hat{N}(\sigma)} f(\sigma) d \sigma+\frac{1}{4 \pi t} \int_{\partial B_{t}(x)} g(\sigma) d \sigma.$$

## Depends on

This node has no prerequisites.

## Proof depends on

- [Corollary 1.0.2 (Representation formula for $\widetilde{U}(t, r ; x)$)](../class-meeting-11/047-t-r-x.md)
- [Proposition 1.0.1 (Spherical averages)](../class-meeting-11/046-spherical-averages.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #12, Section 1](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
