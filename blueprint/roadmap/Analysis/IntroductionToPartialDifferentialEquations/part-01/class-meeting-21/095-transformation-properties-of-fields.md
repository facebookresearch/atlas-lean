---
article_id: af_2f00faba0d81335388551c1a
declaration: def
origin: cited
statement: formalized
lean: FieldTransformation.transformedMetric
---

# Definition 2.0.6 (Transformation properties of fields)

Let $\phi(x)$ be a scalar-valued function, let $m(x)$ be an (invertible) metric (depending on $x$) with components $m_{\mu\nu}(x)$, and let $x \rightarrow \widetilde{x}$ be a spacetime diffeomorphism. Then upon changing coordinates $x \rightarrow \widetilde{x}$, these quantities transform as follows: $\widetilde{\phi}(\widetilde{x}) \coloneqq \phi|_{(x \circ \widetilde{x})}$, $\widetilde{\nabla}_{\mu} \widetilde{\phi}(\widetilde{x}) \coloneqq (M^{-1})_{\mu}^{\alpha}|_{(x \circ \widetilde{x})} \nabla_{\alpha} \phi|_{x \circ \widetilde{x}}$, $\widetilde{m}_{\mu\nu}(\widetilde{x}) \coloneqq (M^{-1})_{\mu}^{\alpha}|_{(x \circ \widetilde{x})} (M^{-1})_{\nu}^{\beta}|_{(x \circ \widetilde{x})} m_{\alpha\beta}|_{(x \circ \widetilde{x})}$, $(\widetilde{m}^{-1})^{\mu\nu}(\widetilde{x}) \coloneqq M_{\alpha}^{\mu}|_{(x \circ \widetilde{x})} M_{\beta}^{\nu}|_{(x \circ \widetilde{x})} (m^{-1})^{\alpha\beta}|_{(x \circ \widetilde{x})}$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #21, Section 2](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
