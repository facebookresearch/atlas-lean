# Revisit-interval bound on undetected-outbreak risk

Let outbreaks at node $i$ of a spreading network arrive as a Poisson process of rate $\lambda_i > 0$, and let $p_i$ be the node impact (the linear upper bound on the expected discounted cost of an outbreak started at $i$), defined from the linearized spreading matrix $A$ and discount rate $r$ with $A - rI$ Hurwitz. Node $i$ is visited at times $t_i(1) < t_i(2) < \dots$, and an outbreak is undetected until the next visit. The risk $R_i$ at node $i$ is the probability of at least one outbreak within a revisit interval times its cost.

**Lemma.** For any interval of length $t$, the probability of at least one Poisson($\lambda_i$) event in it satisfies $1 - e^{-\lambda_i t} \le \lambda_i t$.

**Theorem.** If $A - rI$ is Hurwitz, the risk of an undetected outbreak at every node stays bounded by $R_{\max}$ for any revisit schedule whose intervals satisfy

$$\tau_i = t_i(k+1) - t_i(k) \le \frac{R_{\max}}{p_i \lambda_i + \epsilon_R}$$

for all $i$ and $k$, where $\epsilon_R \ge 0$ is a slack term absorbing the cost accrued during the interval.

Nodes with high impact (high spreading potential to costly nodes) or high outbreak rate must be revisited proportionally more often; combined with a cyclic patrol, the bound turns risk control into a persistent-monitoring scheduling problem.

## Depends on

- [Linear positive-system bound on network SIR cost and node impact](linear-positive-system-bound-on-network-sir-cost-and-node-impact.md)

## Expansion

The lemma is the elementary inequality $1 - e^{-u} \le u$. Over a revisit interval of length $\tau_i$ the probability of an undetected outbreak is at most $\lambda_i \tau_i$, and conditional on an outbreak the expected discounted cost is at most $p_i$ by the positive-system comparison, so $R_i \le (p_i\lambda_i + \epsilon_R)\tau_i$, which is at most $R_{\max}$ under the stated interval bound.

## Sources

- Vera L. J. Somers, Ian R. Manchester, "Minimizing the Risk of Spreading Processes via Surveillance Schedules and Sparse Control", IEEE Transactions on Control of Network Systems 10 (2023), 394–406, <https://doi.org/10.1109/tcns.2022.3203359>. Published version of arXiv:2107.05878, cited next; locators there refer to the arXiv version.
- Vera L. J. Somers, Ian R. Manchester, "Minimizing the Risk of Spreading Processes via Surveillance Schedules and Sparse Control", arXiv (2021). Section 3, Theorem 1, Lemma 5. <https://doi.org/10.48550/arXiv.2107.05878>
