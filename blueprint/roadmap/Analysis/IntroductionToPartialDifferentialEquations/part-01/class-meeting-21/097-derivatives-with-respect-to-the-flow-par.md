---
article_id: af_15080708d31d93e4d3934c98
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: flow_param_derivatives
---

# Proposition 2.0.2 (Derivatives with respect to the flow parameter $\epsilon$)

Let $\widetilde{x}^{\mu}=F_{\epsilon}(x)$ be the change of spacetime coordinates , and let $\widetilde{\phi}, \widetilde{\nabla}_{\mu} \widetilde{\phi}, \widetilde{m}_{\mu\nu}, (\widetilde{m}^{-1})^{\mu\nu}$ be the transformed fields defined in Definition 2.0.6. Then the following identities hold for all spacetime points $\widetilde{x}$: $\partial_{\epsilon}|_{\epsilon=0} \widetilde{\phi}|_{\widetilde{x}} = -Y^{\alpha}|_{\widetilde{x}} \nabla_{\alpha} \phi|_{\widetilde{x}}$, $\partial_{\epsilon}|_{\epsilon=0} \widetilde{\nabla}_{\mu} \widetilde{\phi}|_{\widetilde{x}} = -\nabla_{\mu} Y^{\alpha}|_{\widetilde{x}} \nabla_{\alpha} \phi|_{\widetilde{x}} - Y^{\alpha}|_{\widetilde{x}} \nabla_{\alpha} \nabla_{\mu} \phi|_{\widetilde{x}} = -\nabla_{\mu}(Y^{\alpha} \nabla_{\alpha} \phi)|_{\widetilde{x}}$, $\partial_{\epsilon}|_{\epsilon=0} \widetilde{m}_{\mu\nu}|_{\widetilde{x}} = -m_{\nu\alpha}|_{\widetilde{x}} \nabla_{\mu} Y^{\alpha}|_{\widetilde{x}} - m_{\mu\alpha}|_{\widetilde{x}} \nabla_{\nu} Y^{\alpha}|_{\widetilde{x}} - Y^{\alpha}|_{\widetilde{x}} \nabla_{\alpha} m_{\mu\nu}|_{\widetilde{x}}$, $\partial_{\epsilon}|_{\epsilon=0} (\widetilde{m}^{-1})^{\mu\nu}|_{\widetilde{x}} = (m^{-1})^{\alpha\nu}|_{\widetilde{x}} \nabla_{\alpha} Y^{\mu}|_{\widetilde{x}} + (m^{-1})^{\mu\alpha}|_{\widetilde{x}} \nabla_{\alpha} Y^{\nu}|_{\widetilde{x}} - Y^{\alpha}|_{\widetilde{x}} \nabla_{\alpha}(m^{-1})^{\mu\nu}|_{\widetilde{x}}$, $\partial_{\epsilon}|_{\epsilon=0} \det M^{-1}|_{\widetilde{x}} = -\nabla_{\alpha} Y^{\alpha}|_{\widetilde{x}}$. Above, $\partial_{\epsilon}$ denotes the derivative of an $\epsilon$-dependent quantity with the new coordinates $\widetilde{x}$ held fixed.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #21, Section 2](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
