---
article_id: af_daa8bbe62bd2b1c8246b5972
declaration: def
origin: cited
statement: formalized
lean: ConeSupport.scatteringWavefrontSet
---

# Definition 12.12

If $u \in \mathcal{S}'(\mathbb{R}^{n})$ we define the wavefront set of $u$ to be $\mathrm{WF}(u) = \{(x, \omega) \in \mathbb{R}^{n} \times \mathbb{S}^{n-1} \mid \exists \phi \in \mathcal{C}_{c}^{\infty}(\mathbb{R}^{n}),\, \phi(x) \neq 0,\, \omega \notin \operatorname{Css}(\widehat{\phi u})\}^{\complement}$ and more generally the scattering wavefront set by $\mathrm{WF}_{\mathrm{sc}}(u) = \mathrm{WF}(u) \cup \{(\omega, p) \in \mathbb{S}^{n-1} \times \mathbb{B}^{n} \mid \exists \psi \in \mathcal{C}^{\infty}(\mathbb{S}^{n}),\, \psi(\omega) \neq 0,\, R>0 \text{ such that } p \notin \operatorname{Css}(\widehat{\psi_{R} u})\}^{\complement}$.

## Depends on

- [Definition 9.5](../section-9/066-definition-9-5.md)
- [Definition 12.2](094-definition-12-2.md)

## Sources

- [MIT 18.155 Differential Analysis (Fall 2004), Section 12](../../../../sources/v1/DifferentialAnalysis.md)
