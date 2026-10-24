---
article_id: af_e08ac211fbb22b02c596b630
declaration: def
origin: cited
statement: formalized
lean: contourIntegral
---

# Definition 16.22

Let $f: \Omega \rightarrow \mathbb{C}$ be a continuous function and let $\gamma$ be a curve in $\Omega$. We define the contour integral $$\int_{\gamma} f(z)\, dz \coloneqq \int_a^b f(\gamma(t))\gamma'(t)\, dt$$ whenever the integral on the RHS (which is defined as a Riemann sum in the usual way) converges. Whether $\int_{\gamma} f(z)\, dz$ converges, and if so, to what value, does not depend on the parameterization of $\gamma$: if $\gamma'$ is another parameterized curve with the same (oriented) image as $\gamma$, then $\int_{\gamma'} f(z)\, dz = \int_{\gamma} f(z)\, dz$.

## Depends on

- [Definition 16.21](331-definition-16-21.md)

## Sources

- [MIT 18.785 Number Theory I (Fall 2021), Section 16.3.3](../../../../../../sources/v1/NumberTheoryI.md)
