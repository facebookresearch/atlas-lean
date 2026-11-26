# Reproduction number and subcritical decay in a two-strain model with super-spreaders and waning vaccination

**Model.** A population of constant size $N$ (births $\Lambda = \mu N$ balance natural deaths at rate $\mu$) is split into susceptible $S$, exposed $E$, infectious with an ancestral strain $I_1$, infectious with a more transmissible variant $I_2$, vaccinated $V$, super-spreaders $P$, hospitalized $H$, recovered $R$ and cumulative deaths $F$. The force of infection is

$$

\lambda(t) = \beta(t)\,\frac{I_1 + c_2 I_2 + c_P P}{N},

$$

with time-varying transmission $\beta(t) \ge 0$ and fixed multipliers $c_2, c_P > 0$. Susceptibles are infected at rate $\lambda S$ and vaccinated at rate $w_1(t) S$; vaccinated individuals are infected at rate $(1-\sigma)\lambda V$ with efficacy $\sigma \in [0,1]$ and lose protection at rate $\psi$; recovered individuals lose immunity at rate $\delta$. Exposed individuals leave at rate $\kappa$, entering $I_1$, $I_2$, $P$ with probabilities $\rho_1$, $1 - \rho_1 - \rho_2$, $\rho_2$; strain displacement moves $I_1$ to $I_2$ at rate $m$. Infectious individuals are hospitalized at rate $\gamma_a$, recover at rate $\gamma_i$ (plus strain-specific rates $r_1, r_2$), and die at rates $\delta_i$ ($I_1, I_2$) or $\delta_p$ ($P$). Let

$$

\alpha_1 = \gamma_a + \gamma_i + \delta_i + m + r_1 + \mu,\quad \alpha_2 = \gamma_a + \gamma_i + \delta_i + r_2 + \mu,\quad \alpha_P = \gamma_a + \gamma_i + \delta_p + \mu.

$$

**Theorem (basic reproduction number).** With constant transmission $\beta_0$ and disease-free equilibrium $S^* = N$, the next-generation matrix on $(E, I_1, I_2, P)$ has a single nonzero row and

$$

\mathcal{R}_0 = \frac{\beta_0\kappa}{\mu + \kappa}\left[\frac{\rho_1}{\alpha_1} + c_2\,\frac{1 - \rho_1 - \rho_2}{\alpha_2} + \frac{c_2\, m\,\rho_1}{\alpha_1\alpha_2} + \frac{c_P\,\rho_2}{\alpha_P}\right].

$$

The disease-free equilibrium is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$; for constant inputs $\beta \equiv \beta_0$, $w_1 \equiv w_{1,0}$ and $\mathcal{R}_0 < 1$, the infected compartments decay exponentially and all solutions converge to it.

**Proposition (decay under time-varying suppression).** Let $\beta, w_1 \in L^\infty([0,\infty); \mathbb{R}_{\ge 0})$ and define the effective reproduction number

$$

\mathcal{R}_{\mathrm{eff}}(t) = \mathcal{R}_0(t)\,\frac{S(t) + (1-\sigma)V(t)}{N},

$$

where $\mathcal{R}_0(t)$ is the formula above with $\beta_0$ replaced by $\beta(t)$. If there are $T_0 \ge 0$ and $\rho \in (0,1)$ with $\mathcal{R}_{\mathrm{eff}}(t) \le \rho$ for all $t \ge T_0$, then there exist $M, \gamma > 0$ such that

$$

\|(E, I_1, I_2, P)(t)\|_\infty \le M e^{-\gamma(t - T_0)}\,\|(E, I_1, I_2, P)(T_0)\|_\infty \qquad (t \ge T_0),

$$

and every solution converges to the disease-free equilibrium.

## Depends on

- [$R_0$ as a threshold for the linearized infected subsystem](../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

Ordering the infected states as $(E, I_1, I_2, P)$, new infections enter only $E$, so the new-infection matrix is $\beta_0$ times a matrix whose only nonzero row is $(0, 1, c_2, c_P)$, while the transition matrix is lower triangular with diagonal $(\mu + \kappa, \alpha_1, \alpha_2, \alpha_P)$. The spectral radius of a rank-one, single-row next-generation matrix is its $(1,1)$ entry, which sums the expected infectious periods reached from $E$, weighted by infectiousness; the term $c_2 m \rho_1/(\alpha_1\alpha_2)$ counts ancestral infections displaced into the variant class. For the time-varying case, $S + (1-\sigma)V \le N$ gives the cooperative comparison system $\dot y \le (c(t)\hat T - \Sigma)\,y$ with $c(t) = \beta(t)(S + (1-\sigma)V)/N$; the hypothesis caps $c(t)$ by a constant $c_{\max}$ for which the constant comparison matrix has $\rho(c_{\max}\hat T\Sigma^{-1}) = \rho < 1$, hence negative spectral abscissa, and monotone comparison gives the exponential bound.

## Sources

- Lokman Rachid Melhani, Antonino Sferlazza, Lars Grüne, Dominique Persano Adorno, *A Nine-Compartment Nonlinear Epidemic Model with Spline-Based Identification of Time-Varying Transmission and Vaccination*, arXiv 2026. Section 2.6: theorems "Basic reproduction number" and "Stability of the DFE", propositions "Global convergence of infected states" and "Epidemic decay under time-varying suppression". <https://doi.org/10.48550/arXiv.2606.07413>
