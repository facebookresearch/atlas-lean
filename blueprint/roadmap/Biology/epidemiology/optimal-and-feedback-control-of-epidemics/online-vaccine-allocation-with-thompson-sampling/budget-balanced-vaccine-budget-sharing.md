# Budget-balanced vaccine budget sharing

In the metapopulation SIRD vaccine allocation game, each agent $k$ with budget $B_k(t)$ and vaccination capacity $\Gamma_k$ controls nodes $V_k$. Split new infections at node $i \in V_k$ into internal and external parts,

$$\bar I_i^{\mathrm{in}}(t) = \bar I_i + \beta_i\bar S_i\bar I_i - \gamma_i\bar I_i + \rho\sum_{j\in N_i\cap V_k}p_{ij}\bar I_j, \qquad \bar I_i^{\mathrm{out}}(t) = \rho\sum_{j\in N_i\setminus V_k}p_{ij}\bar I_j,$$

and define the external infection ratio $R_k(t) = \sum_{i\in V_k}\bar I_i^{\mathrm{out}}/\sum_{i\in V_k}(\bar I_i^{\mathrm{in}} + \bar I_i^{\mathrm{out}})$. For $k' \ne k$ let $p^I_{k'k}(t) = \rho\sum_{i\in V_k}\sum_{j\in N_i\cap V_{k'}}p_{ij}\bar I_j(t)$ be the infected flow from agent $k'$ into agent $k$, and set $p^I_{kk}(t) := 0$ by convention (the formula would count infected flows between nodes of one agent; the source's proof asserts that it vanishes). Agent $k'$ shares the fraction $R_{k'}(t)$ of its budget, split in proportion to capacity-weighted infected flows:

$$B^{\mathrm{sh}}_k(t) = B_k(t)\big(1 - R_k(t)\big) + \sum_{k'\neq k}B_{k'}(t)R_{k'}(t)\,\frac{p^I_{kk'}(t)/\Gamma_k}{\sum_{k''}p^I_{k''k'}(t)/\Gamma_{k''}}.$$

**Proposition 1.** The mechanism is budget balanced: $\sum_kB^{\mathrm{sh}}_k(t) = \sum_kB_k(t)$ for every period $t$.

## Depends on

- [Thompson-sampling knapsack vaccine allocation in a metapopulation SIRD model](thompson-sampling-knapsack-vaccine-allocation-in-a-metapopulation-sird-model.md)

## Expansion

Each agent keeps $B_k(1 - R_k)$ and gives away $B_kR_k$, so balance reduces to showing that the received amounts sum to the shared amounts. For a fixed donor $k'$, the split weights $\big(p^I_{kk'}/\Gamma_k\big)/\sum_{k''}p^I_{k''k'}/\Gamma_{k''}$ over recipients $k$ sum to one, because the $k = k'$ term vanishes ($p^I_{k'k'} = 0$ by convention); exchanging the order of summation finishes the proof. The rule sends money toward the agents that seed a donor's external infections, weighted inversely by capacity, so low-capacity agents receive proportionally more. In the global instance most countries lower their own infections and deaths by sharing with high-mobility partners under a fixed total budget.

## Sources

- David Rey, Ahmed W. Hammad, Meead Saberi, "Vaccine allocation policy optimization and budget sharing mechanism using reinforcement learning", Omega 115 (2023), 102783, <https://doi.org/10.1016/j.omega.2022.102783>. Published version of arXiv:2109.10004, cited next; locators there refer to the arXiv version.
- David Rey, Ahmed W. Hammad and Meead Saberi, *Vaccine allocation policy optimization and budget sharing mechanism using Thompson sampling*, arXiv:2109.10004 (2021). <https://doi.org/10.48550/arXiv.2109.10004> Section 5 (budget sharing mechanism, Proposition 1 and its proof).
