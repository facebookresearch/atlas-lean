# Endemic equilibria of the SIS epidemic under prevalence-dependent activation

In the [activity-driven SIS model](degree-based-mean-field-threshold-of-the-activity-driven-sis-epidemic.md), suppose each node chooses whether to activate by comparing a unit activation benefit with an expected infection loss $L\beta d\, \bar x(k)$, where $\bar x(k) = \sum_{t} m_t x_t(k)$ is the publicly known prevalence. In the fully rational limit of the quantal response equilibrium, degree-$d$ susceptible nodes activate exactly when $\bar x(k) \le 1/(L\beta d)$, and infected nodes, whose activation cost $c > 1$ exceeds the benefit, stay inactive. The closed-loop DBMF dynamics are the variable-structure system

$$
x_d(k+1) = \begin{cases} (1-\delta) x_d(k), & \bar x(k) \in \big(\tfrac{1}{L\beta d}, 1\big], \\ (1-\delta) x_d(k) + (1 - x_d(k))\, \beta d \sum_{t} m_t x_t(k), & \bar x(k) \in \big[0, \tfrac{1}{L\beta d}\big]. \end{cases}
$$

**Homogeneous degree.** Let $\mathcal{D} = \{d\}$, $\beta, \delta \in (0,1]$, $\beta d \le 1$. If $\delta \ge \beta d$, then $0$ is the unique equilibrium and attracts $[0,1]$. If $\delta < \beta d$ and $x^*_d = 1 - \delta/(\beta d) \le 1/(L\beta d)$, then $x^*_d$ is a stable endemic equilibrium attracting $(0,1]$. If $\delta < \beta d$ and $x^*_d > 1/(L\beta d)$, then the threshold $1/(L\beta d)$ acts as a sliding surface: prevalence is pinned at the activation threshold.

**Heterogeneous degrees.** Let $d_1 < \dots < d_p$, $\mathcal{D}_j = \{d_1,\dots,d_j\}$, and let $\bar x^{**}(\mathcal{D}_j)$ be the prevalence at the stable equilibrium of the always-active dynamics restricted to $\mathcal{D}_j$ (zero if $\delta \ge \beta\sum_{d \in \mathcal{D}_j} m_d d$). Assume $\beta, \delta \in (0,1]$ and $\beta d_p \le 1$.

1. If $\delta \ge \beta \sum_{d} d\, m_d$, the disease-free state is the unique equilibrium and attracts $[0,1]^p$.
2. Otherwise, let $d_r$ be the largest degree with $\bar x^{**}(\mathcal{D}_r) \le 1/(L\beta d_r)$. A nonzero endemic equilibrium exists if and only if $d_r = d_p$, or $d_r < d_p$ and $\bar x^{**}(\mathcal{D}_r) \in \big(\tfrac{1}{L\beta d_{r+1}}, \tfrac{1}{L\beta d_r}\big]$. It is then $x^*_{d,cl} = x^*_d(\mathcal{D}_r)$ for $d \le d_r$ and $x^*_{d,cl} = 0$ for $d > d_r$.

## Depends on

- [Degree-based mean-field threshold of the activity-driven SIS epidemic](degree-based-mean-field-threshold-of-the-activity-driven-sis-epidemic.md)

## Expansion

When the prevalence exceeds a class's threshold, that class stops activating and its infections decay geometrically. High-degree classes have the lowest thresholds, so at equilibrium only the low-degree classes $\mathcal{D}_r$ remain active. A monotonicity lemma states that adding degree classes to the always-active system can only raise the endemic prevalence. This pins down $d_r$ as the largest class whose threshold is still compatible with its own induced prevalence. Self-protective deactivation therefore holds infection at the edge of the activation threshold instead of eliminating it.

## Sources

- Ashish R. Hota, Tanya Sneh, Kavish Gupta, "Impacts of Game-Theoretic Activation on Epidemic Spread over Dynamical Networks", SIAM Journal on Control and Optimization 60 (2022), S92–S118, <https://doi.org/10.1137/20m1376923>. Published version of arXiv:2011.00445, cited next; locators there refer to the arXiv version.
- Ashish R. Hota, Tanya Sneh, Kavish Gupta, "Impacts of Game-Theoretic Activation on Epidemic Spread over Dynamical Networks", arXiv (2020). Section "A-SIS Epidemic under Game-Theoretic Activation", subsection "Analysis of Closed-Loop Dynamics": homogeneous-degree proposition, always-active SIS proposition, endemic monotonicity proposition and the main closed-loop theorem. <https://doi.org/10.48550/arXiv.2011.00445>
