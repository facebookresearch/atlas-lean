---
article_id: af_91a646beca0ec55ac7824d2c
declaration: def
origin: cited
statement: formalized
lean: taylorExpansion
---

# Definition 8.5

Let $f \in R[x]$ be a polynomial of degree at most $d$ and let $a \in R$. The (degree $d$) Taylor expansion of $f$ about $a$ is $f(x) = f_d(x-a)^d + f_{d-1}(x-a)^{d-1} + \cdots + f_1(x-a) + f_0$ with $f_0, f_1, \ldots, f_d \in R$. The Taylor coefficients $f_0, f_1, \ldots, f_d$ are uniquely determined by the expansion of $f(y+z)$ in $R[y,z]$: $f(y+z) = f_d(y)z^d + f_{d-1}(y)z^{d-1} + \cdots + f_1(y)z + f_0(y)$. Replacing $y$ with $a$ and $z$ with $x-a$ yields the Taylor expansion of $f$ with $f_i = f_i(a) \in R$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.782 Introduction to Arithmetic Geometry (Fall 2013), Section 8.2](../../../../../sources/v1/ArithmeticGeometry.md)
