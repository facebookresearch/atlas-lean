# Forward-Euler stability and dose monotonicity in the log-Gompertz chemotherapy model

**Model.** Let $\mathcal{D}$ be a finite set of cytotoxic drugs and $\mathcal{Q}$ a finite set of cancer cell types. Drug $d$ is administered at rate $U_d(t) \ge 0$ into an effect compartment of volume $\mathscr{V} > 0$ and eliminated at rate $\xi_d > 0$:

$$\dot C_d(t) = -\xi_d\, C_d(t) + \frac{U_d(t)}{\mathscr{V}}, \qquad C_d(0) = 0.$$

Only concentration above a threshold $c_{d,\mathrm{eff}}$ kills: $E_d(t) = \max\{0,\ C_d(t) - c_{d,\mathrm{eff}}\}$. The number $N_q(t)$ of cells of type $q$ follows Gompertz growth with a fractional (log-)kill term whose effectiveness decays at rate $\rho_{d,q} \ge 0$ (acquired resistance):

$$\dot N_q = \Lambda N_q \ln\frac{N_{q,\infty}}{N_q} - \sum_{d \in \mathcal{D}} \eta_{d,q}\, e^{-\rho_{d,q} t}\, N_q\, E_d(t), \qquad \Lambda, \eta_{d,q} > 0.$$

In log-scale $P_q = \ln N_q$ this is the **linear** equation

$$\dot P_q(t) = \Lambda\big(P_{q,\infty} - P_q(t)\big) - \sum_{d \in \mathcal{D}} \eta_{d,q}\, e^{-\rho_{d,q} t}\, E_d(t), \qquad P_{q,\infty} = \ln N_{q,\infty}.$$

**Theorem.**

1. *(Well-posedness.)* If every $U_d$ is continuous on $[0,T]$, the concentration equation and the log-population equation each have a unique solution on $[0,T]$.
2. *(Absolute stability of the Euler schemes.)* Let $h > 0$ be the step size. For a bounded input sequence $(U_s)_{s \ge 0}$ the recursion $C_{s+1} = C_s - h\xi C_s + U_s/\mathscr{V}$ is absolutely stable whenever $h < 2/\xi$; for a bounded forcing sequence $(F_s)_{s \ge 0}$ the recursion $P_{s+1} = P_s + h\big(\Lambda(P_\infty - P_s) - F_s\big)$ is absolutely stable whenever $h < 2/\Lambda$.
3. *(Dose monotonicity.)* Suppose $\Lambda h \le 1$, and consider the discretized model in which the $K$ scenarios $k$ differ only in the initial populations $P^{(k)}_{q,0}$ and the carrying capacities $P^{(k)}_{q,\infty}$. If two feasible effective-concentration profiles satisfy $E^{[1]}_{d,s} \ge E^{[2]}_{d,s}$ for every drug $d$ and step $s \in \{0, \dots, S\}$, then the corresponding end-of-treatment log-populations satisfy $P^{[1],(k)}_{q,S} \le P^{[2],(k)}_{q,S}$ for every cell type $q$ and every scenario $k$, whatever the objective function.

## Depends on

- [Concentration in the one-compartment model](../../../pharmacokinetics/one-compartment-linear-pharmacokinetics/concentration.md)

## Expansion

Both continuous equations are linear with continuous coefficients, so the Picard–Lindelöf theorem applies. Each Euler recursion has the form $x_{s+1} = (1 - h a)x_s + b_s$ with bounded $b_s$; its homogeneous part has amplification factor $1 - ha$, and $|1 - ha| < 1$ exactly when $0 < h < 2/a$, which keeps perturbations from growing. For monotonicity, unroll the log-population recursion:

$$P_{q,S} = (1 - h\Lambda)^S P_{q,0} + \sum_{s=0}^{S-1} (1 - h\Lambda)^{S-1-s}\, h\Big(\Lambda P_{q,\infty} - \sum_{d} \eta_{d,q}\, e^{-\rho_{d,q} t(s)}\, E_{d,s}\Big).$$

With $\Lambda h \le 1$ every weight $(1 - h\Lambda)^{S-1-s}$ is nonnegative and every kill coefficient $\eta_{d,q} e^{-\rho_{d,q} t(s)}$ is positive, so $P_{q,S}$ is a nonincreasing function of each $E_{d,s}$; the initial-population and carrying-capacity terms do not depend on the doses and cancel in the comparison.

## Sources

- Temitayo Ajayi, Seyedmohammadhossein Hosseinian, Andrew J. Schaefer, Clifton D. Fuller, "Combination Chemotherapy Optimization with Discrete Dosing", INFORMS Journal on Computing 36 (2024), 434–455, <https://doi.org/10.1287/ijoc.2022.0207>. Published version of arXiv:2111.02000, cited next; locators there refer to the arXiv version.
- Temitayo Ajayi, Seyedmohammadhossein Hosseinian, Andrew J. Schaefer, Clifton D. Fuller, "Combination Chemotherapy Optimization with Discrete Dosing", arXiv (2021). Section 2 (cell population dynamics, pharmacokinetics, pharmacodynamics) and the theorems of Section 3.3 (Analytical Results). <https://doi.org/10.48550/arXiv.2111.02000>
