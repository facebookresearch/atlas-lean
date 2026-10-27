---
article_id: af_816bce33f727bc1ab60b83a5
declaration: structure
origin: cited
statement: formalized
lean: NullFrame.NullFrameData
---

# Definition 2.2.1

A null frame is a basis for $\mathbb{R}^{1+n}$ consisting of vectors $\{L, \underline{L}, e_{(1)}, \cdots, e_{(n-1)}\}$. Here, $L$ and $\underline{L}$ are null vectors normalized by $m(L, \underline{L})=-2$, and the $e_{(i)}$ are orthonormal vectors that span the $m$-orthogonal complement of $\operatorname{span}(L, \underline{L})$: $m(e_{(i)}, e_{(j)})=\delta_{ij}$, $m(L, e_{(i)})=m(\underline{L}, e_{(i)})=0$, for $1 \leq i \leq j \leq n-1$. Note that the $e_{(i)}$ must form a basis for this complement; i.e., since they are $m$-orthonormal, they must be linearly independent.

## Depends on

- [Definition 2.0.1 (Class Meeting #12, Section 2)](049-definition-2-0-1.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #12, Section 2.2](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
