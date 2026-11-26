# Multinomial air-travel transport operator

Let cities $j = 1, \dots, V$ have populations $N_j > 0$ and let $w_{jl} \ge 0$ be the number of passengers per unit time travelling on the direct connection $j \to l$ ($w_{jj} = 0$). Fix a time step $\Delta t > 0$ with $\sum_l w_{jl}\Delta t \le N_j$ for every $j$, and set

$$p_{jl} \;=\; \frac{w_{jl}\,\Delta t}{N_j}.$$

For a compartment $m$ (susceptible, latent, infectious, recovered, ...) let $X_j^{[m]}$ be its size in city $j$, with $\sum_m X_j^{[m]} = N_j$. In one step, each of the $X_j^{[m]}$ individuals independently travels to city $l$ with probability $p_{jl}$ or stays with probability $1 - \sum_l p_{jl}$, so that the outgoing counts $(\xi^{[m]}_{jl})_{l}$ are multinomial with $X_j^{[m]}$ trials. The stochastic transport operator is the net balance

$$\Omega_j\bigl(X^{[m]}\bigr) \;=\; \sum_{l} \bigl(\xi^{[m]}_{lj} - \xi^{[m]}_{jl}\bigr).$$

Then:

1. $\mathbb{E}[\xi^{[m]}_{jl}] = w_{jl}\Delta t\, X_j^{[m]}/N_j$, $\operatorname{Var}(\xi^{[m]}_{jl}) = X_j^{[m]} p_{jl}(1 - p_{jl})$ and $\operatorname{Cov}(\xi^{[m]}_{jl}, \xi^{[m]}_{jk}) = -X_j^{[m]} p_{jl} p_{jk}$ for $l \ne k$; travellers carry the prevalence of their city of origin.
2. $\mathbb{E}\bigl[\Omega_j(X^{[m]})\bigr] = \Delta t \sum_l \bigl(w_{lj} X_l^{[m]}/N_l - w_{jl} X_j^{[m]}/N_j\bigr)$.
3. Summing over compartments, the expected change of the population of city $j$ is $\Delta t \sum_l (w_{lj} - w_{jl})$; if the traffic matrix is symmetric, $w_{jl} = w_{lj}$, every city population is conserved in expectation, and the total population $\sum_j N_j$ is conserved exactly.

## Expansion

Items 1 and 2 are the first and second moments of a multinomial vector, with success probabilities $p_{jl}$ that do not depend on the compartment. Item 3 follows from $\sum_m X_j^{[m]}/N_j = 1$, and exact conservation of the total holds because every traveller leaves one city and enters another. In the global model the within-city dynamics are Langevin-type stochastic differential equations (one per compartment) coupled through $\Omega_j$, solved with a daily step and a discrete scheme that respects integer counts; a fully discrete multinomial version gives the same results. With 3,100 airports covering about 99% of worldwide airline traffic, the only free parameters are the disease transition rates, because travel flows and populations are fixed by data.

## Sources

- V. Colizza, A. Barrat, M. Barthélemy, A.-J. Valleron, A. Vespignani, "Modeling the worldwide spread of pandemic influenza: baseline case and containment interventions", *PLoS Medicine* 4(1) (2007) e13, Methods, "The Model", <https://doi.org/10.1371/journal.pmed.0040013> (PMC1779816).
