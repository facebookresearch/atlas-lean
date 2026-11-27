# Reproduction number of an SEIPAHRF model with super-spreaders

**Model.** A population of size $N$ is split into susceptible $S$, exposed $E$, symptomatic infectious $I$, super-spreaders $P$, asymptomatic infectious $A$, hospitalised $H$, recovered $R$ and dead $F$ individuals. Infection occurs at rate $\big(\beta I + l\beta H + \beta' P + \beta'' A\big)S/N$, with $l$ the relative infectiousness of hospitalised patients; exposed individuals become infectious at rate $\kappa$ and enter $I$, $P$ or $A$ with probabilities $\rho_1$, $\rho_2$ and $1-\rho_1-\rho_2$. Symptomatic and super-spreading cases are hospitalised at rate $\gamma_a$, recover at rate $\gamma_i$ and die at rates $\delta_i$, $\delta_p$; asymptomatic cases leave at rate $\delta_a$; hospitalised patients recover at rate $\gamma_r$ or die at rate $\delta_h$. Each compartment evolves under a Caputo fractional derivative of its own order $\alpha_\bullet\in(0,1]$ (the integer-order case is $\alpha_\bullet=1$). Write $\varpi_i = \gamma_a+\gamma_i+\delta_i$, $\varpi_p = \gamma_a+\gamma_i+\delta_p$ and $\varpi_h = \gamma_r+\delta_h$.

**Theorem.** The initial value problem has a unique solution, which stays in the biologically feasible region. The basic reproduction number is

$$\mathcal{R}_0 = \frac{\beta\rho_1(\gamma_a l + \varpi_h)}{\varpi_h\varpi_i} + \frac{\rho_2(\beta\gamma_a l + \beta'\varpi_h)}{\varpi_h\varpi_p} + \frac{\beta''(1-\rho_1-\rho_2)}{\delta_a},$$

and the disease-free equilibrium is globally asymptotically stable whenever $\mathcal{R}_0<1$.

## Expansion

The next-generation matrix is the same for every choice of fractional orders, because the equilibria and the sign structure of the linearisation do not depend on $\alpha_\bullet$. Each term counts the secondary infections produced along one route: a symptomatic case infects at rate $\beta$ for mean time $1/\varpi_i$ and, if hospitalised (probability $\gamma_a/\varpi_i$), at rate $l\beta$ for mean time $1/\varpi_h$; a super-spreader infects at rate $\beta'$ for time $1/\varpi_p$ and contributes hospital transmission similarly; an asymptomatic case infects at rate $\beta''$ for time $1/\delta_a$. Global stability for $\mathcal{R}_0<1$ follows from a linear Lyapunov function and fractional comparison arguments.

## Sources

- M. Khalighi, L. Lahti, F. Ndaïrou, P. Rashkov, "Fractional modelling of COVID-19 transmission incorporating asymptomatic and super-spreader individuals", *Mathematical Biosciences* 380 (2025), 109373, Section 4, Theorems 4.1–4.3, <https://doi.org/10.1016/j.mbs.2024.109373> (preprint arXiv:2501.03428).
