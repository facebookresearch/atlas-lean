# Nash link-weight adaptation in the N-intertwined SIS game

**Model.** On a directed network with nodes $i \in \mathcal{N} = \{1, \dots, N\}$, let $p_i(t) \in [0,1]$ be the probability that node $i$ is infected and $\mathcal{N}^{\mathrm{out}}_i$ the set of nodes that $i$ reaches out to, with pre-epidemic weights $a_{ij} > 0$. Node $i$ chooses time-varying weights $w_{ij}(t) \in [0, a_{ij}]$ for $j \in \mathcal{N}^{\mathrm{out}}_i$, and infection follows the directed, weighted, node-dependent N-intertwined SIS dynamics (generalizing the NIMFA equations)

$$\dot p_i = (1 - p_i) \sum_{j \in \mathcal{N}^{\mathrm{out}}_i} w_{ij}\, \beta_j\, p_j - \delta_i p_i ,$$

with infection rates $\beta_j > 0$ and recovery rates $\delta_i > 0$. Each node minimizes over a horizon $[0, T]$ (until a universal remedy such as a patch or vaccine becomes available)

$$J_i = \int_0^T \Big( f_i(p_i(t)) + \sum_{j \in \mathcal{N}^{\mathrm{out}}_i} g_{ij}\big(w_{ij}(t) - a_{ij}\big) \Big)\, dt,$$

where $f_i \colon [0,1] \to \mathbb{R}_{\ge 0}$ is an increasing differentiable infection cost and $g_{ij}$ is a differentiable strictly convex deviation cost minimized at $0$ (the original weights are individually optimal).

**Theorem (equilibrium weight rule).** Let $x_i(t) \in \mathbb{R}^N$ be node $i$'s costate along a Nash equilibrium $(p^*, w^*)$ given by Pontryagin's minimum principle, and set

$$\phi_{ij}(t) = x_{ii}(t)\, \big(1 - p^*_i(t)\big)\, \beta_j\, p^*_j(t).$$

Then for $j \in \mathcal{N}^{\mathrm{out}}_i$,

$$w^*_{ij}(t) = \begin{cases} 0, & -\phi_{ij}(t) \le g_{ij}'(-a_{ij}), \\ a_{ij} + (g_{ij}')^{-1}\big(-\phi_{ij}(t)\big), & g_{ij}'(-a_{ij}) < -\phi_{ij}(t) < g_{ij}'(0), \\ a_{ij}, & -\phi_{ij}(t) \ge g_{ij}'(0). \end{cases}$$

For the quadratic cost $g_{ij}(y) = \tfrac12 y^2$ this is $w^*_{ij} = \min\{a_{ij}, \max\{0, a_{ij} - \phi_{ij}\}\}$.

Reported properties: $x_{ii}(t) \ge 0$ on $[0, T]$ with equality only at $t = T$, so (with all $p^*_j > 0$) every node keeps its links below the original weights until the remedy arrives and restores them at $T$; links to neighbours that are more likely infected ($p_j$ large) or more infectious ($\beta_j$ large) are cut more; and an infected node ($p_i \to 1$) stops cutting its outgoing links. Charging each node a penalty equal to the infection costs of the nodes it can reach aligns the equilibrium with the social optimum of $\sum_i J_i$.

## Depends on

- [NIMFA equations and their spectral epidemic threshold](../n-intertwined-mean-field-approximation/nimfa-equations-and-their-spectral-epidemic-threshold.md)

## Expansion

Node $i$'s Hamiltonian is $H_i = f_i(p_i) + \sum_j g_{ij}(w_{ij} - a_{ij}) + \sum_m x_{im}\, \dot p_m$, and $w_{ij}$ enters $\dot p$ only through $\dot p_i$, contributing $x_{ii}(1 - p_i)\beta_j p_j\, w_{ij} = \phi_{ij} w_{ij}$. Minimizing the convex function $w \mapsto g_{ij}(w - a_{ij}) + \phi_{ij} w$ over $[0, a_{ij}]$ gives the stationarity condition $g_{ij}'(w - a_{ij}) = -\phi_{ij}$, projected onto the interval: the minimizer is $0$ when the derivative is already nonnegative at $w = 0$ and $a_{ij}$ when it is still nonpositive at $w = a_{ij}$. The costates solve the linear adjoint system $\dot x_i = \Lambda(t)\, x_i + \lambda_i$ with $\lambda_i = -\nabla f_i$ and terminal condition $x_i(T) = 0$, in which $\Lambda$ is assembled from the equilibrium weights and infection probabilities. For a concave deviation cost the rule becomes bang-bang between $0$ and $a_{ij}$.

## Sources

- Y. Huang and Q. Zhu, "Game-theoretic frameworks for epidemic spreading and human decision-making: a review", Dynamic Games and Applications 12 (2022), 7–48, Eqs. (23)–(27) and Theorem 2, <https://doi.org/10.1007/s13235-022-00428-0> (PMCID: PMC8853398).
- Y. Huang and Q. Zhu, "A differential game approach to decentralized virus-resistant weight adaptation policy over complex networks", IEEE Transactions on Control of Network Systems 7 (2020), 944–955.
