# Thompson-sampling knapsack vaccine allocation in a metapopulation SIRD model

**Metapopulation SIRD model.** Nodes $i$ (regions) with population $P_i$ and neighbors $N_i$ in a mobility network with flows $f_{ij}$ have flow rates $p_{ij} = f_{ij}/\sum_{j'}f_{ij'}$ and global flow-to-population ratio $\rho = \sum_{i,j}f_{ij}/\sum_iP_i$. Compartment fractions evolve in discrete time as

$$\bar S_i(t+1) = \bar S_i(t) - \beta_i\bar S_i(t)\bar I_i(t) + \rho\sum_{j\in N_i}p_{ij}\big(\bar S_j(t) - \bar S_i(t)\big),$$

$$\bar I_i(t+1) = \bar I_i(t) + \beta_i\bar S_i\bar I_i - \gamma_i\bar I_i + \rho\sum_{j\in N_i}p_{ij}\big(\bar I_j - \bar I_i\big),$$

with recovered fraction gaining $(1 - \lambda_i)\gamma_i\bar I_i$ plus mobility exchange and $\bar D_i = 1 - \bar S_i - \bar I_i - \bar R_i$. The model assumes balanced flows $p_{ij}P_i = p_{ji}P_j$ and outflow proportional to population.

**Allocation problem.** Agent $k$ controls nodes $V_k$ and chooses vaccination fractions $x_i(t) \in [0,\bar x_i(t)]$. Vaccinating node $i$ multiplies its susceptibles by $1 - \theta_ix_i$, where $\theta_i$ is an unknown mean vaccine efficiency in $[0,1]$. Assuming worst-case zero vaccination at other agents' nodes, the expected number of susceptibles at $t+1$ is affine in $x$, and agent $k$ solves the knapsack linear program

$$\min\ \mathbb{E}\Big[\sum_{i\in V_k}l_i(t)\,x_i(t)\Big] \quad \text{s.t.}\quad \sum_{i\in V_k}C_ix_i(t) \le B_k(t), \quad 0 \le x_i(t) \le \bar x_i(t),$$

where the loss coefficient $l_i(t)$ collects all terms multiplying $x_i$ and depends on $\theta$.

**Thompson-sampling policy.** Each node carries a $\mathrm{Beta}(a_i,b_i)$ belief (initially uniform). Each period: sample $\hat\theta_i \sim \mathrm{Beta}(a_i,b_i)$; substitute into $l_i$ to get $\hat l_i$; solve the deterministic fractional knapsack greedily by sorting nodes by $\hat l_i/C_i$ in increasing order; update caps $\bar x_i(t) = 1 - \sum_{t'=\max\{t - m_i + 1,1\}}^{t}x_i(t')$ with $m_i = \lceil P_i/\sum_jf_{ji}\rceil$; observe Bernoulli($\theta_i$) outcomes at vaccinated nodes and increment $a_i$ on success, $b_i$ on failure.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

Because the one-step objective is linear in $x$ with a single budget constraint and box constraints, the relaxed problem is a fractional knapsack, solved exactly by the ratio greedy rule in $O(|V_k|\log|V_k|)$. Thompson sampling handles the exploration–exploitation trade-off in learning efficiencies, following the Beta–Bernoulli bandit analysis of Agrawal and Goyal. The cap $\bar x_i$ accounts for the turnover of susceptibles by mobility: a node whose inflow is large relative to its population needs repeated vaccination sooner. In the global COVID-19 instance, the policy reduces susceptibles, infections and deaths relative to population-proportional allocation.

## Sources

- David Rey, Ahmed W. Hammad, Meead Saberi, "Vaccine allocation policy optimization and budget sharing mechanism using reinforcement learning", Omega 115 (2023), 102783, <https://doi.org/10.1016/j.omega.2022.102783>. Published version of arXiv:2109.10004, cited next; locators there refer to the arXiv version.
- David Rey, Ahmed W. Hammad and Meead Saberi, *Vaccine allocation policy optimization and budget sharing mechanism using Thompson sampling*, arXiv:2109.10004 (2021). <https://doi.org/10.48550/arXiv.2109.10004> Section 3.2 (metapopulation SIRD model) and Section 4 (allocation formulation, knapsack reformulation and the Thompson-sampling algorithm).
