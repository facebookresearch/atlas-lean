---
article_id: af_3c67a375df231b2f55023d27
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: schwarz_poisson
---

# Theorem 2 (Schwarz' Theorem)

Let $U$ be a real piecewise continuous function on $|z| = 1$ and define the Poisson integral $u(z) = P_{U}(z)$ by $$u(a) = \frac{1}{2\pi} \int_{0}^{2\pi} \frac{1 - |a|^{2}}{|a - e^{i\varphi}|^{2}}\, U(e^{i\varphi})\, d\varphi, \quad |a| < 1.$$ Then $u$ is harmonic, and $$\lim_{z \to e^{i\varphi_{0}}} u(z) = U(e^{i\varphi_{0}})$$ if $U$ is continuous at $e^{i\varphi_{0}}$.

## Depends on

- [Definition 1 (Lecture 16: Harmonic Functions)](025-definition-1.md)

## Sources

- [MIT 18.112 Functions of a Complex Variable (Fall 2008), Lecture 16: Harmonic Functions, Schwarz' Theorem](../../../../sources/v1/ComplexVariables.md)
