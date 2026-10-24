---
article_id: af_d845ac5acabdfe936f1be450
declaration: theorem
origin: cited
lean: CM18.proposition_2_0_1_ode_flow
---

# Proposition 2.0.1 (Basic facts from ODE theory for autonomous systems)

Let $Y(x)=(Y^{0}(x^{0}, \cdots, x^{n}), Y^{1}(x^{0}, \cdots, x^{n}), \cdots, Y^{n}(x^{0}, \cdots, x^{n}))$ be a smooth vectorfield on $\mathbb{R}^{1+n}$. Assume that there exists a uniform constant $C>0$ such that $|\nabla_{\mu} Y^{\nu}(x)| \leq C$, $x \in \mathbb{R}^{1+n}$, $0 \leq \mu, \nu \leq n$. Consider the initial value problem for the system of ordinary differential equations: $\frac{d}{d\epsilon} \widetilde{x}^{\mu}(\epsilon) = Y^{\mu}(\widetilde{x})$, $\widetilde{x}^{\mu}(0) = x^{\mu}$. Then there exists a number $\epsilon_{0}>0$ such that the initial value problem has a unique smooth (in $\epsilon$) solution existing on the interval $\epsilon \in [-\epsilon_{0}, \epsilon_{0}]$. Let us denote the flow map from the data $x$ to the solution $\widetilde{x}$ at flow parameter $\epsilon$ by $\widetilde{x}=F_{\epsilon}(x)$. Then on the interval $[-\epsilon_{0}, \epsilon_{0}]$, the flow map $x \rightarrow F_{\epsilon}(x) \coloneqq \widetilde{x}$ is a smooth (in $x$), bijective map from $\mathbb{R}^{1+n}$ to $\mathbb{R}^{1+n}$ with smooth inverse $F_{-\epsilon}(\cdot)$, i.e., $\widetilde{x}=F_{\epsilon}(x) \Longrightarrow x=F_{-\epsilon}(\widetilde{x})$; such maps are called diffeomorphisms of $\mathbb{R}^{1+n}$. Furthermore, if $|\epsilon_{1}|+|\epsilon_{2}| \leq \epsilon_{0}$, then the flow map verifies the one-parameter commutative group properties: $F_{\epsilon_{1}} \circ F_{\epsilon_{2}}=F_{\epsilon_{2}} \circ F_{\epsilon_{1}}=F_{\epsilon_{1}+\epsilon_{2}}$. Let us also denote the derivative matrix corresponding to the flow map $F_{\epsilon}$ by $M$: $M_{\nu}^{\mu} \coloneqq \frac{\partial \widetilde{x}^{\mu}}{\partial x^{\nu}}$. Then if $|\epsilon|$ is sufficiently small, we have the following expansions in $\epsilon$: $\widetilde{x}^{\mu} = x^{\mu}+\epsilon Y^{\mu}(x)+\epsilon^{2} \mathcal{R}^{\mu}(\epsilon, x)$, $M_{\nu}^{\mu} = \delta_{\nu}^{\mu}+\epsilon \nabla_{\nu} Y^{\mu}(x)+\epsilon^{2} \nabla_{\nu} \mathcal{R}^{\mu}(\epsilon, x)$, $(M^{-1})_{\nu}^{\mu} = \delta_{\nu}^{\mu}-\epsilon \nabla_{\nu} Y^{\mu}(x)+\epsilon^{2} \mathcal{S}_{\nu}^{\mu}(\epsilon, x)$, $\det M^{-1} = 1-\epsilon \nabla_{\alpha} Y^{\alpha}+\epsilon^{2} \mathcal{S}(\epsilon, x)$. Above, $\mathcal{R}^{\mu}(\epsilon, x), \nabla_{\nu} \mathcal{R}^{\mu}(\epsilon, x), \mathcal{S}_{\nu}^{\mu}(\epsilon, x), \mathcal{S}(\epsilon, x)$ are smooth functions of $(\epsilon, x)$ for $\epsilon \in [-\epsilon_{0}, \epsilon_{0}]$, $x \in \mathbb{R}^{1+n}$.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.152 Introduction to Partial Differential Equations (Fall 2011), Class Meeting #21, Section 2](../../../../../sources/v1/IntroductionToPartialDifferentialEquations.md)
