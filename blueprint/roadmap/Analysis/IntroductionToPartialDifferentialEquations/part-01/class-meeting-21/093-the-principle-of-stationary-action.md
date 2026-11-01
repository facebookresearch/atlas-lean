---
article_id: af_f3d80b179c41793ac11bae01
declaration: theorem
origin: cited
lean: CM18.euler_lagrange_equation
---

# Theorem 1.1 (The Principle of Stationary Action)

Let $\mathcal{L}(\phi, \nabla \phi, x)$ be a $C^{2}$ Lagrangian. Then a $C^{2}$ field $\phi$ is a stationary point of the action if and only if the following Euler-Lagrange PDE is verified by $\phi$: $$\nabla_{\alpha}\left(\frac{\partial \mathcal{L}(\phi, \nabla \phi, x)}{\partial(\nabla_{\alpha} \phi)}\right)=\frac{\partial \mathcal{L}(\phi, \nabla \phi, x)}{\partial \phi}.$$ Above, $\frac{\partial \mathcal{L}(\phi, \nabla \phi, x)}{\partial(\nabla_{\alpha} \phi)}$ denotes partial differentiation of $\mathcal{L}$ with respect to its argument $\nabla_{\alpha} \phi$ with its other arguments (e.g., the other $\nabla_{\mu} \phi$ with $\mu \neq \alpha$, $\phi$, $x$, etc.) held fixed.

## Depends on

- [Definition 1.0.5 (Definition of a stationary point $\phi$)](092-definition-of-a-stationary-point-phi.md)

## Proof depends on

- [Definition 1.0.2 (Action)](089-action.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #21, Section 1](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
