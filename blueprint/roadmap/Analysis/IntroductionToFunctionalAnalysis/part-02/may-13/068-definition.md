---
article_id: af_c5748cfc577f27d988f8c37d
declaration: def
origin: cited
statement: formalized
lean: SpectralTheory.greensOperatorSqrt
---

# Definition (May 13, 2021)

Let $f \in L^2([0, 1])$, and suppose that $f(x) = \sum_{k=1}^{\infty} c_k \sqrt{2} \sin(k \pi x)$, where $c_k = \int_0^1 f(x) \sqrt{2} \sin (k \pi x) \, dx$. Then we define the linear operator $A^{1/2}$ via $A^{1/2}f(x) = \sum_{k=1}^{\infty} \frac{1}{k\pi} c_k \sqrt{2} \sin (k\pi x)$.

## Depends on

- [Definition ($L^p$ space)](../../part-01/april-6/045-l-p-space.md)
- [Theorem (May 13, 2021)](066-theorem.md)

## Sources

- [MIT 18.102 Introduction to Functional Analysis (Spring 2021), May 13, 2021](../../../../../sources/v1/IntroductionToFunctionalAnalysis.md)
