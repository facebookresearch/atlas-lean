---
article_id: af_e1331ef3d4181d04bcd5e217
declaration: theorem
origin: cited
lean: meanCurvature_parametric_eq_levelSet
---

# Proposition 25.4

Let $M \subset \mathbb{R}^{n+1}$ be a hypersurface. Take a point $y \in M$, a local defining function $\psi$ for $M$ near $y$, and an orthonormal basis $Y_{1}, \ldots, Y_{n}$ of the tangent space $TM_{y}$. Then $\kappa_{\text{mean}} = \pm \frac{1}{\|\nabla \psi_{y}\|} \sum_{i=1}^{n} \langle Y_{i}, D^{2} \psi_{y} \cdot Y_{i} \rangle$ and $\kappa_{\text{gauss}} = \pm \frac{\operatorname{det}(D^{2} \psi_{y} \cdot Y_{1}, \ldots, D^{2} \psi_{y} \cdot Y_{n}, \nabla \psi_{y})}{\|\nabla \psi_{y}\|^{n+1}}$.

## Depends on

- [Definition 12.1](../chapter-2/040-definition-12-1.md)
- [Definition 14.4](../chapter-2/049-definition-14-4.md)
- [Definition 24.1](../lecture-24/077-definition-24-1.md)

## Proof depends on

- [Definition 12.3](../chapter-2/042-definition-12-3.md)
- [Definition 12.4](../chapter-2/043-definition-12-4.md)
- [Definition 12.5](../chapter-2/044-definition-12-5.md)

## Sources

- [MIT 18.950 Differential Geometry (Fall 2008), Lecture 25](../../../../../sources/v1/DifferentialGeometry.md)
