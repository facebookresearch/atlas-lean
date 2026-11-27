# Cost-to-go certificates for spreading on temporal-switching networks

Let a spreading process run on a sequence of graphs $\mathcal{G}^k = (\mathcal{V},\mathcal{E}^k)$, $k = 1,\dots,K$, with known time-varying spreading rates $\beta^k_{ij} \ge 0$ and recovery rates $\delta^k_i$. With time step $h > 0$ the discrete-time linearized (upper-bounding) model is the positive system $x^{k+1} = A^k x^k$ with

$$a^k_{ii} = 1 - h\delta^k_i \ge 0, \qquad a^k_{ij} = h\beta^k_{ij} \ \ ((i,j) \in \mathcal{E}^k), \qquad a^k_{ij} = 0 \ \text{otherwise},$$

and the discounted finite-horizon cost is $J(x^1) = \sum_{k=1}^K \alpha^k C x^k$ with non-negative row vector $C$ and discount $\alpha \in (0,1]$.

**Proposition (finite horizon).** If there are elementwise non-negative row vectors $p^1,\dots,p^K$ (with $p^{K+1} := 0$) such that

$$p^k \ge C + \alpha\, p^{k+1} A^k, \qquad k = 1,\dots,K,$$

elementwise, then $p^1 x^1 \ge J(x^1)$ for every $x^1 \ge 0$.

**Proposition (infinite horizon).** If future networks are dominated by the last one, $A^K \ge A^k$ for all $k \ge K$, and the inequalities hold for $k = 1,\dots,K-1$ together with $p^K \ge C + \alpha p^K A^K$, then $p^1 x^1$ bounds the cost summed over all $k \ge 1$.

**Proposition (convexity of sparse resource allocation).** Let resources reduce spreading rates within $[\underline{\beta}^k_{ij}, \overline{\beta}^k_{ij}]$ and raise recovery rates within $[\underline{\delta}^k_i, \overline{\delta}^k_i] \subset [0,\overline{\Delta})$ through exponential cost models $u_{ij} = f_{ij}(\beta_{ij})$, $v_i = g_i(\overline{\Delta} - \delta_i)$, under per-step budgets $\Gamma^k$ and a total budget $\Gamma_{\mathrm{tot}}$. If $h\overline{\Delta} < 1$, then minimizing the worst-node risk bound $\max_i \hat{x}^1_i p^1_i$ (or minimizing total resources subject to a risk bound) is equivalent, under $y^k_i = \log p^k_i$, to an exponential cone program in $(y,u,v)$; its $\ell_1$-type budget constraints promote sparse allocations, and reweighted $\ell_1$ iterations approximate minimum-cardinality allocations.

## Depends on

- [Linear positive-system bound on network SIR cost and node impact](linear-positive-system-bound-on-network-sir-cost-and-node-impact.md)

## Expansion

Define $V(x^k, k) = p^k x^k$. Since $x^k \ge 0$ and $p^k \ge C + \alpha p^{k+1}A^k$, one gets $V(x^k,k) \ge Cx^k + \alpha V(x^{k+1},k+1)$; telescoping from $k = 1$ to $K$ with $p^{K+1} = 0$ gives $p^1 x^1 \ge \sum_k \alpha^{k-1} C x^k \ge J(x^1)$ for $\alpha \le 1$. For the infinite horizon, $A^K \ge A^k$ and $p^K \ge 0$ give $p^K \ge C + \alpha p^K A^k$ for all later $k$, so the same telescoping continues indefinitely. After the log transformation each constraint $p^k_j \ge c_j + \alpha\sum_i p^{k+1}_i a^k_{ij}$ becomes a log-sum-exp inequality, which is convex, and the resource models enter linearly in the exponents.

## Sources

- Vera L.J. Somers, Ian R. Manchester, "Sparse Resource Allocation for Spreading Processes on Temporal-Switching Networks", IFAC-PapersOnLine 56 (2023), 7387–7393, <https://doi.org/10.1016/j.ifacol.2023.10.356>. Published version of arXiv:2302.02079, cited next; locators there refer to the arXiv version.
- Vera L. J. Somers, Ian R. Manchester, "Sparse Resource Allocation for Spreading Processes on Temporal-Switching Networks", arXiv (2023). Section 2 (model and cost), Proposition 1, Section 3 propositions (exponential cone reformulations), Subsections "Sparsity" and "Infinite Time". <https://doi.org/10.48550/arXiv.2302.02079>
