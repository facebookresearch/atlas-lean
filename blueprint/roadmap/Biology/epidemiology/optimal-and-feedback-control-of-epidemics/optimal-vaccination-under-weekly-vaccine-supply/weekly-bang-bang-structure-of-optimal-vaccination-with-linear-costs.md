# Weekly bang-bang structure of optimal vaccination with linear costs and supply constraints

**Setting.** A population is split into $K$ groups (regions or ages) of sizes $n_i > 0$. In group $i$, $s^{(i)}$ is the susceptible fraction, $x^{(i)} \in \mathbb{R}^d$ the fractions in the disease stages (exposed, infectious, ...), and vaccination at rate $u_i(t) \ge 0$ moves susceptibles to the vaccinated pool:

$$\dot s^{(i)} = -s^{(i)} f_i(\boldsymbol{x}) - u_i s^{(i)}, \qquad \dot x^{(i)} = s^{(i)} f_i(\boldsymbol{x})\,e_1 + g(x^{(i)}), \qquad \dot V = \sum_{i=1}^K u_i\,n_i\,s^{(i)},$$

with $f_i \ge 0$ the force of infection, $g$ the within-group progression ($\sum_j g_j = 0$, $g(0) = 0$, essentially nonnegative). Vaccination capacity gives the mixed constraint $0 \le u_i s^{(i)} \le v_i^{\max}$; weekly shipments of at most $V_w^{\max}$ doses give the cumulative supply $D(t) = \sum_{m \le w} V_m^{\max}$ on $[7w, 7(w+1))$, smoothed to $D_\epsilon$ equal to $D$ away from $\epsilon/2$-neighbourhoods of shipment days, and the pure state constraint $V(t) \le D_\epsilon(t)$. The cost is linear in the vaccination total and in a per-capita health cost $f_0 \ge 0$:

$$J[u] = c_v\,V(T) + \sum_{i=1}^K \int_0^T n_i\, f_0\big(x^{(i)}(t)\big)\,dt, \qquad c_v > 0.$$

**Theorem.** Solutions exist, are unique, stay nonnegative with $s^{(i)} \ge l_i > 0$, and the problem has a global minimiser whose Pontryagin multiplier is normal ($\lambda_0 > 0$). Assume further that $f_i$, $f_0$ and $g$ are linear with $\beta_{ij} = \nabla_{x^{(i)}} f_j \ge 0$, $\nabla f_0 \ge 0$, $Dg$ Metzler, that vaccination reaches at least one cost-bearing state, and that $f_i(\boldsymbol{x}(t)) > 0$. Then on every week window $W_{w,\epsilon} = [7w + \epsilon,\, 7(w+1) - \epsilon]$:
1. (Shadow prices.) The adjoints satisfy $\psi_1^{x^{(i)}}(t) < \psi_i^{s}(t) < 0$, $\dot\psi_i^s > 0$, $\dot\psi_1^{x^{(i)}} \ge 0$.
2. (No singular arcs.) There is no open interval on which $0 < u_i s^{(i)} < v_i^{\max}$ almost everywhere, so each group is vaccinated either at full capacity or not at all.
3. (One switch per week.) If group $i$ is vaccinated at some time in the week, vaccination started at the beginning of the week; once it stops it stays off for the rest of the week; and when the stock is exhausted ($V = D_\epsilon$) vaccination stops immediately.

## Expansion

The linear cost makes the Hamiltonian affine in each $u_i$, so the optimal rate is decided by the sign of a switching function built from the adjoints of $s^{(i)}$, of the first disease stage, of the stock $V$ and the state-constraint multiplier. Linearity and the Metzler structure make the adjoint system cooperative, which gives the strict ordering of shadow prices: a newly infected individual is costlier than a susceptible, and both shadow prices relax monotonically towards zero as the horizon approaches. That monotonicity makes the switching function strictly monotone within a week, ruling out singular arcs and permitting at most one switch, from full-rate vaccination to none, between consecutive shipments. The mixed constraint is turned into a box constraint $u_i \le v_i^{\max}/l_i$ by the lower bound on $s^{(i)}$, which gives compactness and existence by Cesari's theorem.

## Sources

- Lucas M. Moschen, M. Soledad Aronna, "Bang-Bang Optimal Control of Vaccination in Metapopulation Epidemics With Linear Cost Structures", IEEE Control Systems Letters 9 (2025), 492–497, <https://doi.org/10.1109/lcsys.2025.3575227>. Published version of arXiv:2503.15154, cited next; locators there refer to the arXiv version.
- Lucas Machado Moschen, Maria Soledad Aronna, "Bang-Bang Optimal Control of Vaccination in Metapopulation Epidemics with Linear Cost Structures", arXiv:2503.15154 (2025), Section 2 (model, constraints and cost), Propositions 1–3, Assumption 1, Lemma 1, Theorems 1 and 2, <https://doi.org/10.48550/arXiv.2503.15154>.
