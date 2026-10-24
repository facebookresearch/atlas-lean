---
article_id: af_a3ec97b4e6eae447092d2b57
declaration: def
origin: cited
statement: formalized
lean: SurfaceArea.surfaceArea
---

# Definition 3 (Lecture 13, Section 3.2)

Let $K$ be a body. The surface area of $K$ is defined as the differential rate of volume increase as we add a small Euclidean ball to the body, i.e., $S(K) = \operatorname{Vol}(\partial K) = \lim_{\epsilon \to 0} \frac{\operatorname{Vol}(K \oplus \epsilon B_2^n) - \operatorname{Vol}(K)}{\epsilon}$.

## Depends on

- [Definition 6 (Section 6)](../section-6/100-definition-6.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 13, Section 3.2](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
