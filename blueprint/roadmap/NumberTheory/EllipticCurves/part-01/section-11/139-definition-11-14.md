---
article_id: af_1c52e31e6c3ec96e954d3807
declaration: structure
origin: cited
statement: formalized
lean: PrimalityCertificate
---

# Definition 11.14

A primality certificate for $p$ is a tuple of integers $(p, A, B, x_1, y_1,
 q)$, where $P = (x_1 : y_1 : 1)$ is a point on the elliptic curve $E: y^2 =
 x^3 + Ax + B$ over $\mathbb{Q}$, the integer $p > 1$ is prime to
 $\Delta(E)$, and $qP$ is zero $\bmod p$ with $q > (p^{1/4}+1)^2$.

## Depends on

- [Definition 11.12](137-definition-11-12.md)

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 11.2](../../../../../sources/v1/EllipticCurves.md)
