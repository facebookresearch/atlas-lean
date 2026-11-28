# Redundancy of birth and death rates for fractional dynamics of SIR-type models

**Projection formula.** Let $\dot Y = V(Y)$ be a compartment model on $Y \in \mathbb{R}^n_{\ge0}$ with constant per-capita demographic rates, i.e. the total $N = \sum_i Y_i$ satisfies $\dot N = \sum_i \nu_i Y_i$ ($\nu_i$ = birth minus death rate of compartment $i$). With $Q_{ijk} = \frac12[\delta_{ij}(\nu_k - \nu_j) + \delta_{ik}(\nu_j - \nu_k)]$ and $Q_i(Y) = \sum_{j,k}Q_{ijk}Y_jY_k$,

$$\frac{\dot N}{N}Y_i = \nu_iY_i + \frac1N Q_i(Y),$$

so the fractions $y = Y/N$ obey $\dot y_i = F_i(y)$ with $F_i(Y) = V_i(Y) - \nu_iY_i - Q_i(Y)/N$, the projection of $V$ onto the leaves of constant population.

**Master model.** Two susceptible classes $\mathbb{S}_1, \mathbb{S}_2$ and infected $\mathbb{I}$: births $B = \delta_1\mathbb{S}_1 + \delta_2\mathbb{S}_2 + (1 - p_I)\delta_I\mathbb{I}$ enter $\mathbb{S}_i$ in proportions $q_i$ (a fraction $p_I$ of births to infected are infected), deaths at rates $\mu_1, \mu_2, \mu_I$, switching $\mathbb{S}_1 \leftrightarrow \mathbb{S}_2$ at rates $\alpha_1, \alpha_2$, standard incidence $\beta_i\mathbb{S}_i\mathbb{I}/N$, recovery from $\mathbb{I}$ into $\mathbb{S}_i$ at rates $\gamma_i$. Let $\nu_i = \delta_i - \mu_i$, $\nu_I = \delta_I - \mu_I$.

**Theorem.** If $\nu_1 = \nu_2 =: \nu$, the fractions $S_i = \mathbb{S}_i/N$, $I = \mathbb{I}/N$ satisfy the demography-free system

$$\dot S_1 = -\tilde\alpha_1S_1 + \tilde\alpha_2S_2 + \tilde\gamma_1I - \tilde\beta_1S_1I, \quad \dot S_2 = \tilde\alpha_1S_1 - \tilde\alpha_2S_2 + \tilde\gamma_2I - \tilde\beta_2S_2I, \quad \dot I = (\tilde\beta_1S_1 + \tilde\beta_2S_2)I - (\tilde\gamma_1 + \tilde\gamma_2)I,$$

with shifted parameters

$$\tilde\alpha_1 = \alpha_1 + q_2\delta_1,\ \ \tilde\alpha_2 = \alpha_2 + q_1\delta_2,\ \ \tilde\gamma_i = \gamma_i + q_i(1 - p_I)\delta_I,\ \ \tilde\beta_i = \beta_i + \nu_I - \nu.$$

All birth and death rates are thus absorbed into the remaining parameters, and two models with the same shifted parameters have isomorphic fractional dynamics. With $\Delta\nu_I = \nu - \nu_I$ (excess mortality of infecteds) and $\tilde\beta_1 > \tilde\beta_2$: if $\Delta\nu_I < \beta_2$ the variable-population model is isomorphic to a constant-population model with transmission coefficients $\beta_i - \Delta\nu_I > 0$; if $\Delta\nu_I > \beta_2$ it is isomorphic to a model in which one transmission coefficient becomes an extra recovery flow. Consequently several published SIRS/SIS/vaccination models with varying population (e.g. those of Li–Ma and of Avram et al.) have isomorphic fractional dynamics.

## Proof sketch

Since $\frac{d}{dt}(Y_i/N) = (V_i - Y_i\dot N/N)/N$ and $\dot N/N$ is linear in $Y/N$, demographic terms become linear (births redistribute fractions) or quadratic with coefficients $\nu_j - \nu_k$ (differential growth of compartments). When all susceptible classes grow at the same per-capita rate, the only surviving quadratic term is $(\nu_I - \nu)S_iI$, which has the same form as standard incidence and shifts $\beta_i$; the linear birth flows simply add to switching and recovery rates. A negative shifted transmission coefficient is reinterpreted as a recovery-like flow, which accounts for the dichotomy in the theorem.

## Sources

- Florian Nill, "On the Redundancy of Birth and Death Rates in Homogeneous Epidemic SIR Models", *Fractal and Fractional* 7 (2023), 313, <https://doi.org/10.3390/fractalfract7040313>. Preprint version: arXiv:2302.04223 (2023), Section 2 (constant per-capita demographic rates and the projection lemma), Section 3 (three-compartment master model and its proposition), Section 4 (isomorphisms between models from the literature), <https://doi.org/10.48550/arXiv.2302.04223>.
