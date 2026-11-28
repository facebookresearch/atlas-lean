# Linear cost-to-go bounds and convex sparse resource allocation for network SIS spreading

**Model.** On a graph with $n$ nodes, the discrete-time mean-field SIS dynamics are

$$
x_i^{k+1} = x_i^k + h(1 - x_i^k)\sum_{j} \beta_{ij} x_j^k - h\delta_i x_i^k,
$$

which keep $x^k \in [0,1]^n$ when $h\delta_i \le 1$ and $h\sum_j \beta_{ij} < 1$. The **risk** of an outbreak is the discounted cost $J(x^1) = \sum_{k \ge 1} \alpha^k C x^k$, with nonnegative row vector $C$ and $\alpha \in (0,1]$. At each stage $k = 1,\dots,K$, resources may lower edge spreading rates within $\underline\beta_{ij}^k \le \beta_{ij}^k \le \bar\beta_{ij}^k$ or raise recovery rates within $\underline\delta_i^k \le \delta_i^k \le \bar\delta_i^k < \bar\Delta$, and the changes persist. Linearizing at the disease-free state gives the positive system $x^{k+1} = A^k x^k$ with $a^k_{ii} = 1 - h\delta_i^k$ and $a^k_{ij} = h\beta_{ij}^k$ for edges $(i,j)$.

**Proposition (dynamic-programming bound).** Suppose there are elementwise nonnegative row vectors $p^1,\dots,p^K$ with

$$
p^k \ge C + \alpha\, p^{k+1} A^k \quad (k = 1,\dots,K-1), \qquad p^K \ge C + \alpha\, p^K A^K.
$$

Then $p^1 x^1 \ge J(x^1)$ for the nonlinear dynamics as well as the linear one. So linear cost-to-go functions certify upper bounds on outbreak risk.

**Proposition (convex reformulation).** Suppose $h\bar\Delta < 1$. Substitute $y_i = \log p_i$, encode the reductions as $u_{ij} = f_{ij}(\beta_{ij})$ and $v_i = g_i(\bar\Delta - \delta_i)$ (logarithmic resource models whose costs lie in $[0, w_{ij}\log(\bar\beta_{ij}^k/\underline\beta_{ij}^k)]$ and $[0, w_{ii}\log((1 - \underline\delta_i^k)/(1 - \bar\delta_i^k))]$). Then both problems below become convex exponential-cone programs:

1. minimizing the certified risk bound $\max_i(\log \hat x_i^1 + y_i^1)$ under per-stage resource budgets;
2. minimizing the total resource $\sum_{ij} u_{ij}^k + \sum_i v_i^k$ subject to a certified risk bound $\log \hat x_i^1 + y_i^1 \le \gamma$.

The $\ell_1$-type resource costs promote sparse allocations.

## Depends on

- [Spectral radius and die-out of SIS epidemics](../../sis-extinction-times-on-finite-graphs/prob-ne-empty-le.md)

## Expansion

Since $(1 - x_i) \le 1$, the nonlinear trajectory is dominated componentwise by the linear positive system. Positive systems with nonnegative linear stage costs admit linear value functions. Unrolling the inequalities gives $p^1 x^1 \ge \sum_k \alpha^k C x^k$, and the stationary tail inequality $p^K \ge C + \alpha p^K A^K$ bounds the infinite horizon. The constraints are posynomial in $p$ and in the transformed rates, so the exponential change of variables turns the bilinear dynamic-programming inequalities into log-sum-exp constraints, which are convex.

## Sources

- Vera L. J. Somers, Ian R. Manchester, "Multi-Stage Sparse Resource Allocation for Control of Spreading Processes over Networks", in 2022 American Control Conference (ACC) (2022), 3632–3639, <https://doi.org/10.23919/acc53348.2022.9867834>. Published version of arXiv:2110.07755, cited next; locators there refer to the arXiv version.
- Vera L. J. Somers, Ian R. Manchester, "Multi-Stage Sparse Resource Allocation for Control of Spreading Processes over Networks", arXiv (2021). Section 2 (model and problems), Proposition 1, Proposition 2, Proposition 3. <https://doi.org/10.48550/arXiv.2110.07755>
