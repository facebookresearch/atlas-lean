---
article_id: af_e47fe78103fcd2f311b038ba
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: NullFrame.nullFrame_decomposition_full
---

# Proposition 2.2.1 (Null frame decomposition of $m$)

If $\{L, \underline{L}, e_{(1)}, \cdots, e_{(n-1)}\}$ is a null frame, then we can decompose
$$m_{\mu \nu}=-\frac{1}{2} L_{\mu} \underline{L}_{\nu}-\frac{1}{2} \underline{L}_{\mu} L_{\nu}+h_{\mu \nu}$$
where $h_{\mu \nu}$ is positive-definite on the $m$-orthogonal complement of $\operatorname{span}(L, \underline{L})$, and $h_{\mu \nu}$ vanishes on $\operatorname{span}(L, \underline{L})$.

Similarly, by raising each index on both sides with $m^{-1}$, we have that
$$(m^{-1})^{\mu \nu}=-\frac{1}{2} L^{\mu} \underline{L}^{\nu}-\frac{1}{2} \underline{L}^{\mu} L^{\nu}+p^{\mu \nu}.$$

## Depends on

- [Definition 2.2.1](053-definition-2-2-1.md)

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #12, Section 2.2](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
