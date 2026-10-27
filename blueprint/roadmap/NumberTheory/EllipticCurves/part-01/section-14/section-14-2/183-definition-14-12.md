---
article_id: af_75bf26d5d7891fc2821c4e8e
declaration: def
origin: cited
statement: formalized
lean: SmoothCurve.contourIntegral
---

# Definition 14.12

For a smooth curve $\gamma:[a, b] \rightarrow \mathbb{C}$ and a complex
 function $f(z)$ defined on an open set containing $\gamma$ the contour
 integral of $f$ along $\gamma$ is defined by $$\int_{\gamma} f(z)
 dz\coloneqq\int_{a}^{b} f(\gamma(t)) \gamma'(t) dt$$ This definition extends
 to piecewise smooth curves in the obvious way (sum the contour integrals on
 each smooth piece).

## Depends on

- [Definition 14.11](182-definition-14-11.md)

## Sources

- [MIT 18.783 Elliptic Curves (Spring 2021), Section 14.2](../../../../../../sources/v1/EllipticCurves.md)
