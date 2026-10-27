---
article_id: af_448cb666e1aeb9547098eb9f
declaration: theorem
origin: cited
statement: formalized
lean: SpaceCurves.frenetSerret_theorem
---

# Theorem 6.1

For a Frenet curve $c$ in $\mathbb{R}^{n}$, let $E(t)$ be the matrix with columns $e_{1}(t), \ldots, e_{n}(t)$. We have $\frac{d}{dt} E(t) = \left\|c^{\prime}(t)\right\| E(t) \left(\begin{array}{cccc} 0 & -\kappa_{1}(t) & 0 & \cdots \\ \kappa_{1}(t) & 0 & -\kappa_{2}(t) & \cdots \\ 0 & \kappa_{2}(t) & 0 & -\kappa_{3}(t) \cdots \\ \cdots & & & \end{array}\right)$. Here $\kappa_{1}(t), \ldots, \kappa_{n-2}(t) > 0$, and $\kappa_{n-1}(t) \in \mathbb{R}$. Concretely, $\kappa_{i}(t) = \frac{\langle e_{i+1}(t), e_{i}^{\prime}(t) \rangle}{\left\|c^{\prime}(t)\right\|}$. The functions $\kappa_{i}(t)$ are called the Frenet curvatures of $c$. They are reparametrization invariant.

## Depends on

- [Definition 5.3](../chapter-1-lecture-5/017-definition-5-3.md)

## Sources

- [MIT 18.950 Differential Geometry (Fall 2008), Chapter 1, Lecture 6](../../../../../../sources/v1/DifferentialGeometry.md)
