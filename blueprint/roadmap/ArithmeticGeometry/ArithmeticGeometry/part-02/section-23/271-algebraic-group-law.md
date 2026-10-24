---
article_id: af_525f0d284a58ada3b0152ec9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: WeierstrassCurve.Affine.Point.explicit_chord_formula
---

# Theorem 23.20 (Algebraic group law)

Let $E / k$ be an elliptic curve given by the short Weierstrass equation $y^{2}=x^{3}+a_{4} x+a_{6}$. If $P_{1}=(x_{1}: y_{1}: 1)$ and $P_{2}=(x_{2}: y_{2}: 1)$ are affine points whose sum is an affine point $P_{3}=(x_{3}: y_{3}: z_{3})$, then $x_{3}=\lambda^{2}-x_{1}-x_{2}$ and $y_{3}=\lambda(x_{1}-x_{3})-y_{1}$ where $\lambda=(y_{2}-y_{1})/(x_{2}-x_{1})$ if $P_{1} \neq P_{2}$ and $\lambda=(3x_{1}^{2}+a_{4})/(2y_{1})$ if $P_{1}=P_{2}$.

## Depends on

- [Definition 23.12](264-definition-23-12.md)
- [Definition 23.14](266-definition-23-14.md)
- [Theorem 23.16](267-theorem-23-16.md)

## Proof depends on

- [Corollary 23.19 (Geometric group law)](270-geometric-group-law.md)

## Sources

- [MIT 18.782 Introduction to Arithmetic Geometry (Fall 2013), Section 23.3](../../../../../sources/v1/ArithmeticGeometry.md)
