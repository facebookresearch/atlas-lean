---
article_id: af_5edd94a147ca38e2fdb1c710
declaration: structure
origin: cited
statement: formalized
lean: MovingFrame.IsMovingBasis
---

# Definition 18.1

Let $f \colon U \rightarrow \mathbb{R}^{n+1}$ be a hypersurface patch. A moving basis for $f$ is a collection $(X_{1}, \ldots, X_{n})$ of vector-valued functions $X_{i} \colon U \rightarrow \mathbb{R}^{n}$ which are linearly independent at each point. If the $X_{i}$ are orthonormal with respect to the first fundamental form, we call $(X_{1}, \ldots, X_{n})$ a moving frame. Let $X$ be the matrix whose columns are $(X_{1}, \ldots, X_{n})$, and define the connection matrices and their curvature matrices to be, respectively, $A_{j} = X^{-1}(\partial_{x_{j}} X) + X^{-1} \Gamma_{j} X$ and $F_{kj} = \partial_{k} A_{j} - \partial_{j} A_{k} + A_{k} A_{j} - A_{j} A_{k}$.

## Depends on

- [Definition 12.1](../chapter-2/040-definition-12-1.md)
- [Definition 12.3](../chapter-2/042-definition-12-3.md)
- [Definition 16.1](../lecture-16/051-definition-16-1.md)

## Sources

- [MIT 18.950 Differential Geometry (Fall 2008), Lecture 18](../../../../../sources/v1/DifferentialGeometry.md)
