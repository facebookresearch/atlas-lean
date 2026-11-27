# Growth equation of a balanced growth state

**Setting (growth balance analysis).** A cell grows exponentially at rate $\mu$ with constant concentrations. Its $n$ active reactions are described by an active stoichiometric matrix $A \in \mathbb{R}^{(m+1)\times n}$ in mass-fraction units: row $P$ is the net production of total protein, rows $\alpha = 1, \dots, m$ the net production of reactants, and every column is mass balanced (negative entries sum to $-1$, positive entries to $+1$, unless the reaction exchanges mass with the exterior). Let $v \in \mathbb{R}^n$ (all $v_j \neq 0$) be the fluxes, $y = [P, a]^{\mathsf T} \in \mathbb{R}^{m+1}_{>0}$ the total protein and reactant mass concentrations, $p \in \mathbb{R}^n_{>0}$ the concentrations of the catalysing proteins, and $k_j(a) \neq 0$ given kinetic functions. A **balanced growth state** (BGS) at $y$ is a flux vector satisfying

$$A v = \mu\, y, \qquad P = \sum_{j=1}^n p_j, \qquad v_j = p_j\, k_j(a) \quad (j = 1, \dots, n).$$

An **elementary growth state** (EGS) is a BGS that is an elementary flux mode (support-minimal feasible flux vector) of the linear problem obtained by freezing the composition $y$ and the effective rate constants $k_j(a)$.

**Theorem.**
1. *(Uniqueness along a direction.)* For fixed $y$ and any $v'$ with $A v' \propto y$ and $k_j v'_j > 0$ for all $j$, there is exactly one BGS of the form $\lambda v'$, $\lambda > 0$; if some $k_j v'_j \le 0$ there is none.
2. *(Decomposition.)* Every BGS at $y$ is a weighted average $\sum_l w_l v^{(l)}$ ($w_l > 0$, $\sum_l w_l = 1$) of EGSs at the same $y$, and its growth rate is the same weighted average of their growth rates.
3. *(Full rank.)* The active stoichiometric matrix of an EGS has full column rank $n$.
4. *(Investment and growth equations.)* Suppose $A$ is square and invertible (no dependent reactants), and write $x = [P, a]^{\mathsf T}$. Then

$$v = \mu\, A^{-1} x, \qquad p_j = \frac{\mu \sum_i (A^{-1})_{ji}\, x_i}{k_j(a)}, \qquad \mu(x) = \frac{P}{\displaystyle\sum_{j}\sum_{i} \frac{(A^{-1})_{ji}\, x_i}{k_j(a)}},$$

where $i$ ranges over $\{P, 1, \dots, m\}$. Conversely, $x$ supports a BGS with active matrix $A$ if and only if the value $\mu(x)$ given by this formula and all the resulting $p_j$ are positive. For a general $A$ of full column rank the same formulas hold with $A^{-1}$ replaced by $B^{-1}$, where $B$ is an invertible $n \times n$ submatrix of rows of $A$ and $x$ is the corresponding vector of independent concentrations.

## Expansion

Part 1 holds because the mass balance $Av = \mu y$ is homogeneous in $(v, \mu)$ while the protein sum fixes the scale. Part 2 follows from the decomposition of a feasible flux vector of an irreversible flux cone into elementary flux modes, each rescaled to a BGS by part 1; the weights must sum to one because only one BGS lies on each ray. Part 3 is the support-minimality of elementary modes. For part 4, multiply $Av = \mu x$ by $A^{-1}$; the entry $(A^{-1})_{ji}$ is the share of flux $v_j$ invested in offsetting the growth dilution of component $i$, so $A^{-1}$ is called the investment (dilution) matrix. Dividing by $k_j$ gives the protein concentrations, and summing them to $P$ solves for $\mu$. Thus, once the active reaction set is known, fluxes, proteome and growth rate are explicit functions of the concentrations alone, which is what makes marginal costs and benefits of each concentration computable.

## Sources

- H. Dourado, M. J. Lercher, "An analytical theory of balanced cellular growth", Nature Communications 11 (2020) 1226, Results (Eqs. (1)–(6)) and Methods (Definitions 1–3, Theorems 1–7), <https://doi.org/10.1038/s41467-020-14751-w>, PMCID: PMC7060212.
