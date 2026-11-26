# Transport PDE limit of stochastic structured population models

Let the trait space be $E = E_1 \cup E_2$, where $E_1$ is a finite set of compartments and $E_2 = \bigcup_{i \in I_2} \{i\}\times\bar{\mathcal{X}}_i$ is a finite union of compartments carrying a continuous trait in the closure of an open connected set $\mathcal{X}_i \subset \mathbb{R}^{d_i}$. Individuals in compartment $i \in I_2$ follow the flow of a smooth vector field $F^i$, and individuals in $E_1$ do not move; the reference measure is $\lambda = \sum_{x\in E_1}\delta_x + \sum_{i\in I_2}\delta_i\otimes \mathrm{Leb}(\bar{\mathcal{X}}_i)$. The flow generator is $A_\varphi h(i,x) = \nabla h(i,x)\cdot F^i(x)$ on $E_2$ and $0$ on $E_1$, with distributional adjoint $A^*_\varphi m = -\sum_i \mathrm{div}_i(m F^i)$.

Let $\xi_t$ solve the weak large-population equation of the stochastic structured population model, under the mass-control and Lipschitz-kernel assumptions. If $\xi_0 \ll \lambda$ and every jump kernel $k_i(m,x)$ is absolutely continuous with respect to $\lambda$ with measurable density $k_i(m,x,z)$, then $\xi_t \ll \lambda$ for all $t \in [0,T]$ and its density $\xi(t,x)$ is a weak solution of the transport equation

$$ \partial_t \xi(t,x) + \sum_{i\in I_2} \mathrm{div}_i\big(\xi(t,\cdot) F^i\big)(x) = \int \xi(t,x') \sum_i \alpha_i(\xi_t, x')\, k_i(\xi_t, x', x)\, \lambda(dx') , $$

whose right-hand side collects births, deaths and transitions as a nonlocal source term.

## Depends on

- [Law of large numbers for stochastic structured population models](law-of-large-numbers-for-stochastic-structured-population-models.md)

## Expansion

Absolute continuity is preserved because the push-forward $\varphi_t\sharp\lambda$ is absolutely continuous with respect to $\lambda$ (compartments in $E_1$ are fixed and the flow on each $\mathcal{X}_i$ has a Jacobian), and the jump term only adds absolutely continuous measures, so absolute continuity propagates along the weak equation. Taking test functions compactly supported in each $\mathcal{X}_i$ in the weak equation and moving the derivative onto the density gives the PDE.

## Sources

- P. Carmona, "Some deterministic structured population models which are limit of stochastic individual based models", arXiv:1804.04913 (2018), Section 4 (the associated PDE; Theorem 4.1), Section 5.4 (proof) and Section 6 (age-structured SIR and host–pathogen examples). <https://doi.org/10.48550/arXiv.1804.04913>
