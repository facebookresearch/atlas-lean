---
article_id: af_0ca189e7202f969a906f08c0
declaration: theorem
origin: cited
statement: formalized
lean: UniformSet.uniformization_lemma
---

# Lemma (Uniformization)

Let $\delta = \Delta^m$, $X \subset [0,1]^d$, and let $\mu$ be an arbitrary sub-additive set function (e.g., $\mu(B) = |B|_\delta$). Then there exists a subset $Y \subset X$ such that $Y$ is $(\Delta, m)$-uniform and $$\mu(Y) \geq \left[2 d \ln\!\left(\frac{1}{\Delta}\right)\right]^{-m} \mu(X) = \delta^{-\sigma} \mu(X)$$ where $\sigma = \frac{\ln(2 \ln \frac{1}{\Delta})}{\ln \frac{1}{\Delta}}$.

## Depends on

- [Definition (Section: Bourgain's Projection Theorem II)](075-definition.md)

## Sources

- [MIT 18.156 Projection Theory (Spring 2025), Section: Bourgain's Projection Theorem II](../../../../../sources/v1/ProjectionTheory.md)
