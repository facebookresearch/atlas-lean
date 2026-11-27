# Balance equation of optimal density-constrained growth

**Setting.** Use the growth balance analysis setting of a balanced growth state with square invertible active stoichiometric matrix $A$ (no dependent reactants), independent concentrations $x = [P, a]^{\mathsf T} \in \mathbb{R}^{m+1}_{>0}$, kinetic functions $k_j(a)$, proteome fractions $\phi_j = p_j / P$, and growth rate $\mu(x)$ given by the growth equation. Assume growth rate determines fitness and define, for each $i \in \{P, 1, \dots, m\}$ and each reaction $j$,

$$\eta_i = \frac{1}{\mu}\frac{\partial \mu}{\partial x_i} \quad\text{(marginal net benefit)}, \qquad q_{ij} = \frac{1}{P}\Big(\frac{\partial p_j}{\partial x_i}\Big)_{\mu,\,k_j} = \frac{\mu\,(A^{-1})_{ji}}{P\,k_j} \quad\text{(marginal production cost)},$$

$$u_{\alpha j} = -\frac{1}{P}\Big(\frac{\partial p_j}{\partial a_\alpha}\Big)_{v_j} = \frac{p_j}{P}\,\frac{1}{k_j}\frac{\partial k_j}{\partial a_\alpha} \quad\text{(marginal kinetic benefit)}.$$

**Theorem.**

1. *(Net benefits.)* $\eta_P = \dfrac{1}{P} - \sum_j q_{Pj}$ and $\eta_\alpha = \sum_j \big(u_{\alpha j} - q_{\alpha j}\big)$. Equivalently, $\eta_i = -\sum_j \big(\partial \phi_j / \partial x_i\big)_{\mu}$: at fixed growth rate, raising $x_i$ by $\Delta x_i$ lowers the total proteome fraction needed by $\eta_i\,\Delta x_i$.
2. *(Optimal states are elementary.)* Impose the dry-mass density limit $\rho \ge P + \sum_\alpha a_\alpha$. A density-constrained balanced growth state with maximal growth rate is an elementary growth state, and the density constraint is active at the optimum.
3. *(Balance equation.)* Let $\mu^*(\rho)$ be the maximal growth rate and $\eta_\rho = \dfrac{1}{\mu^*}\dfrac{d\mu^*}{d\rho}$. At an optimal density-constrained state,

    $$\eta_i = \eta_\rho \qquad \text{for every } i \in \{P, 1, \dots, m\}.$$

    With dependent reactants $c_\gamma = D_{\gamma P} P + \sum_\beta D_{\gamma\beta} b_\beta$, this becomes $\eta_i = \kappa_i\,\eta_\rho$ for each independent concentration, with density factor $\kappa_i = 1 + \sum_\gamma D_{\gamma i}$ and $\eta_i$ the total marginal net benefit.

## Expansion

Part 1 differentiates the growth equation $\mu = P / \sum_j \sum_i (A^{-1})_{ji} x_i / k_j(a)$: increasing a concentration raises the dilution flux every upstream protein must offset (cost $q$) and, for a reactant, speeds the reactions it saturates (benefit $u$); total protein also accelerates every reaction linearly, contributing $1/P$. Part 2 compares the nonlinear optimum with the protein-constrained flux balance problem at the optimal composition, whose optima are elementary flux modes. Part 3 is the Lagrange condition for maximizing $\mu(x)$ on the hyperplane $P + \sum_\alpha a_\alpha = \rho$: if one concentration had a higher marginal benefit than another, shifting density towards it would raise growth. The $n = m + 1$ balance equations and the active density constraint form $n + 1$ equations for the $n$ concentrations and $\eta_\rho$, so growth optimization reduces to solving them. Applied to the ribosome reaction with its ternary-complex substrate, the condition $\eta_T = \eta_P$ predicts the growth-rate dependence of ribosomal proteome fractions in *E. coli* and yeast without fitted parameters, and a minimal transporter-plus-ribosome cell gives $\rho\,\eta_\rho \approx 0.66$.

## Depends on

- [Growth equation of a balanced growth state](growth-equation-of-a-balanced-growth-state.md)

## Sources

- H. Dourado, M. J. Lercher, "An analytical theory of balanced cellular growth", Nature Communications 11 (2020) 1226, Results (Eqs. (7)–(10)) and Methods (Definitions 4–5, Theorems 8–10, Eq. (42)), <https://doi.org/10.1038/s41467-020-14751-w>, PMCID: PMC7060212.
