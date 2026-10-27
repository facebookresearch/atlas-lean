---
article_id: af_16c36f493a75f397c0c5f364
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: CM9.Wave.dAlembert_uniqueness
---

# Theorem 4.1 (d'Alembert's formula)

Assume that $f \in C^{2}(\mathbb{R})$ and $g \in C^{1}(\mathbb{R})$. Then the unique solution $u(t, x)$ to $-\partial_{t}^{2} u(t, x)+\partial_{x}^{2} u(t, x)=0$ with initial data $u(0, x)=f(x)$, $\partial_{t} u(0, x)=g(x)$ satisfies $u \in C^{2}([0, \infty) \times \mathbb{R})$ and can be represented by d'Alembert's formula: $u(t, x)=\frac{1}{2}(f(x+t)+f(x-t))+\frac{1}{2} \int_{z=x-t}^{z=x+t} g(z) d z$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #10, Section 4](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
