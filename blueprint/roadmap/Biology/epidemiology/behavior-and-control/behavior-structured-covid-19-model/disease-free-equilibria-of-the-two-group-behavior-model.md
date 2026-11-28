# Disease-free equilibria of the two-group behavior model

**Model.** The population is divided into behavioral groups (here two: group 1 and group 2, differing in adherence to mitigation measures), each with susceptible, exposed, symptomatic, asymptomatic, hospitalized and recovered classes. Individuals move between groups at behavior-change rates; at the disease-free baseline the influence of group 1 on group 2 is $c^B_{12}$ and of group 2 on group 1 is $c^B_{21}$. Infection is driven by symptomatic, asymptomatic and hospitalized individuals. Define the control reproduction number and the relative influence ratio

$$\mathcal{R}_c = \theta_l\Bigl(\frac{r\beta_i}{\sigma_i} + \frac{(1-r)\beta_a}{\gamma_a} + \frac{rq\beta_h}{\gamma_h + \delta_h}\Bigr), \qquad \Gamma = \frac{c^B_{12}}{c^B_{21}},$$

where $\theta_l$ scales contacts under interventions, $r$ is the symptomatic fraction, $q$ the hospitalized fraction of symptomatic cases, $\beta_{i,a,h}$ the class-specific transmission rates and $\sigma_i, \gamma_a, \gamma_h + \delta_h$ the exit rates of the infectious classes.

**Theorem.** Besides the trivial extinction state, there are three non-trivial disease-free equilibria.
- The group-1-only DFE is stable if $\mathcal{R}_c < 1$ and $\Gamma > 1$, and unstable if $\mathcal{R}_c > 1$ or $\Gamma \le 1$.
- The group-2-only DFE is stable if $\mathcal{R}_c < 1$ and $\Gamma < 1$, and unstable if $\mathcal{R}_c > 1$ or $\Gamma \ge 1$.
- The coexistence DFE is stable if $\mathcal{R}_c < 1$ and $\Gamma = 1$, and unstable if $\mathcal{R}_c > 1$ or $\Gamma \ne 1$.

All solutions with non-negative data remain non-negative and bounded.

## Depends on

- [Solutions of the Kermack-McKendrick SIR model](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

The Jacobian at each DFE is block triangular: an infection block whose stability is governed by the next-generation number $\mathcal{R}_c$, and a behavior block governing how the two groups exchange members in the absence of disease. Using Metzler-matrix stability (a Metzler matrix is Hurwitz iff a related next-generation spectral radius is below one), the behavior block reduces to a competition between groups in which the group with the larger influence ratio takes over; a tie $\Gamma = 1$ is the knife edge that allows coexistence. Disease control therefore needs $\mathcal{R}_c < 1$, while which behavior prevails at the disease-free state is decided by social influence alone.

## Sources

- A. Oveson, M. Girvan, A. Gumel, "Modeling the impact of hospitalization-induced behavioral changes on the spread of COVID-19 in New York City", *Infectious Disease Modelling* 10(4) (2025), 1055–1092, Theorem 3.1, Eq. (eq:RC), Theorems 4.4-4.6, <https://doi.org/10.1016/j.idm.2025.05.001> (preprint arXiv:2501.06941).
