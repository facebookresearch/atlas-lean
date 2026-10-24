---
article_id: af_b10f59af45c9db60e01080bc
declaration: theorem
origin: cited
lean: taylor_complex
---

# Theorem 1 (Taylor's Theorem)

If $f(z)$ is analytic in a region $\Omega$ containing $a$, one has $$f(z) = f(a) + \frac{f'(a)}{1!}(z-a) + \cdots + \frac{f^{(n-1)}(a)}{(n-1)!}(z-a)^{n-1} + f_{n}(z)(z-a)^{n},$$ where $f_{n}(z)$ is analytic in $\Omega$. Moreover, if $C$ is the boundary of a closed disk contained in $\Omega$ with center $a$, then $f_{n}(z)$ has the representation $$f_{n}(z) = \frac{1}{2\pi i} \int_{C} \frac{f(\zeta)\, d\zeta}{(\zeta - a)^{n}(\zeta - z)} \quad (z \text{ inside } C).$$

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.112 Functions of a Complex Variable (Fall 2008), Lecture 10, Remarks on Lecture 10](../../../../sources/v1/ComplexVariables.md)
