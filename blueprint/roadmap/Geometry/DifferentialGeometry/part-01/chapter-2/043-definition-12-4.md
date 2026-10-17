---
article_id: af_f33c18aa309fcbeb07217bce
declaration: def
origin: cited
statement: formalized
lean: secondFundamentalForm
---

# Definition 12.4

Define $H_{ij}(x) = -\langle \partial_{x_{i}} \nu, \partial_{x_{j}} f \rangle = \langle \partial_{x_{i}} \partial_{x_{j}} f, \nu(x) \rangle$. Equivalently, the matrix with entries $H_{ij}(x)$ is $H_{x} = -D\nu_{x}^{\mathrm{tr}} \cdot Df_{x}$. The associated symmetric bilinear form, $II_{x}(X, Y) = \langle X, H_{x} Y \rangle = -\langle D\nu_{x}(X), Df_{x}(Y) \rangle = \langle \nu(x), D^{2}f_{x}(X, Y) \rangle$, is called the second fundamental form.

## Depends on

- [Definition 12.1](040-definition-12-1.md)

## Proof depends on

- [Definition 12.2](041-definition-12-2.md)

## Sources

- [MIT 18.950 Differential Geometry (Fall 2008), Chapter 2, Lecture 12](../../../../../sources/v1/DifferentialGeometry.md)
