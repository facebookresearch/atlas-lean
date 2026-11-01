---
article_id: af_c980b1471dcfd302b08141ba
declaration: def
origin: cited
statement: formalized
lean: QuadraticFormEquiv.matrixToQuadraticForm
---

# Definition 9.1

The four equivalent definitions below all define a quadratic form on $k$. 1. A homogeneous quadratic polynomial $f \in k[x_{1}, \ldots, x_{n}]$. 2. Associated to $f$ is a symmetric matrix $A \in k^{n \times n}$ whose entries $(a_{ij})$ correspond to the coefficients of $x_{i} x_{j}$ in $f$ via $f(x_{1}, \ldots, x_{n})=\sum_{i,j} a_{ij} x_{i} x_{j}$. Conversely, every symmetric matrix defines a homogeneous quadratic polynomial. 3. Each symmetric matrix $A$ defines a symmetric bilinear form $B: k^{n} \times k^{n} \rightarrow k$ via $B_{f}(x, y)=x^{t} A y$. Conversely, if $B$ is a symmetric bilinear form, and $e_{1}, \ldots, e_{n}$ are basis vectors, the matrix $A=(a_{ij})$ defined by $a_{ij}=B(e_{i}, e_{j})$ is symmetric. 4. The function $f: k^{n} \rightarrow k$ obtained by evaluating a homogeneous quadratic polynomial is a homogeneous quadratic function. In terms of the corresponding bilinear form $B(x, y)$, we have $f(x)=B(x, x)$. Conversely, we can recover $B(x, y)$ from $f(x)$ via $B(x, y)=\frac{f(x+y)-f(x)-f(y)}{2}$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.782 Introduction to Arithmetic Geometry (Fall 2013), Section 9.1](../../../../../sources/v1/ArithmeticGeometry.md)
