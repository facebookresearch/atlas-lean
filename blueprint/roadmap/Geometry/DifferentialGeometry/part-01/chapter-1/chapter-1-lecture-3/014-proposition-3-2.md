---
article_id: af_0679e0e05cbbb14463603349
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: PlaneCurves.curvature_level_set_full
---

# Proposition 3.2

Let $f \colon U \rightarrow \mathbb{R}$ be a smooth function, defined on an open subset $U \subset \mathbb{R}^{2}$. Let $c \colon I \rightarrow U$ be a regular curve, which is contained in its level set $\{f(x) = a\}$. Then, at every point $t$ such that $x = c(t)$ satisfies $\nabla f(x) \neq 0$, we have $\pm \kappa(t) = \frac{\langle J \nabla f(x),\, D^{2} f(x)\, J \nabla f(x) \rangle}{\|\nabla f(x)\|^{3}}$. Here, $D^{2} f(x)$ is the Hessian (the matrix of second derivatives). The sign is determined as follows. If $\operatorname{det}\left(\nabla f(x), c^{\prime}(t)\right) > 0$, then $\kappa(t)$ is the right hand side of the equation above. Otherwise, $-\kappa(t)$ is the right hand side.

## Depends on

- [Definition 1.2](../chapter-1-lecture-1/002-definition-1-2.md)

## Sources

- [MIT 18.950 Differential Geometry (Fall 2008), Chapter 1, Lecture 3](../../../../../../sources/v1/DifferentialGeometry.md)
