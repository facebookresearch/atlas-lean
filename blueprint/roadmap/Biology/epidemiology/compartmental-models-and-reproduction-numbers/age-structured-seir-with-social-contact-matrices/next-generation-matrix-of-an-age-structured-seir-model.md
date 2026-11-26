# Next-generation matrix of an age-structured SEIR model

**Model.** Divide a population into age groups $i = 1, \dots, n$ of sizes $n_i$, with $S_i, E_i, I_i, R_i$ the numbers susceptible, exposed, infectious and recovered. Let $B_{ij}(t) \ge 0$ be the mean number of contacts per unit time that an individual in group $i$ makes with individuals in group $j$, and let every contact carry the same transmission rate $\tau$. The force of infection on group $i$ is

$$\lambda_i(t) = \tau \sum_{j} B_{ij}(t)\, \frac{I_j}{n_j},$$

and

$$\dot S_i = -\lambda_i S_i, \quad \dot E_i = \lambda_i S_i - \nu E_i, \quad \dot I_i = \nu E_i - g I_i, \quad \dot R_i = g I_i,$$

with latent-to-infectious rate $\nu$ and recovery rate $g$. Contacts are reciprocal in aggregate: $n_i B_{ij} = n_j B_{ji}$. Time dependence of $B$ (for example term time versus school holidays) is piecewise constant.

**Proposition.** For a fixed contact matrix $B$ and susceptible numbers $S_i$, the next-generation matrix has entries

$$M_{ij} = \frac{\tau}{g}\, B_{ij}\, \frac{S_i}{n_j} = \frac{\tau}{g}\, B_{ji}\, \frac{S_i}{n_i},$$

the expected number of new infections in group $i$ caused by one infectious individual in group $j$, and the reproduction number is its spectral radius $R = \rho(M)$. At the start of an epidemic with no prior immunity $S_i = n_i$; with pre-existing immunity in a fraction $\pi_i$ of group $i$, $S_i = (1 - \pi_i)n_i$. The disease-free state is unstable if and only if $R > 1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Linearize at the disease-free state with infected compartments $(E_i, I_i)$. New infections enter $E_i$ at rate $\tau S_i \sum_j B_{ij} I_j / n_j$, and transitions are $E_i \to I_i$ at rate $\nu$ and removal from $I_i$ at rate $g$. In the van den Driessche–Watmough decomposition the infectious period has mean $1/g$ and the latent stage is passed with probability one, so the reduced next-generation matrix on the $I$ compartments is $M$; the latent period changes the growth rate but not $R$. The second expression for $M_{ij}$ uses reciprocity. Because $R$ scales linearly in $\tau$ and $B$, the ratio of $R$ under two contact matrices (term time versus holidays) depends only on the contact data, which is how measured changes in mixing can be tested against observed changes in epidemic growth.

## Sources

- Eames KT, Tilston NL, Brooks-Pollock E, Edmunds WJ, "Measured dynamic social contact patterns explain the spread of H1N1v influenza" (2012), Methods, "Dynamic Disease Model" (force of infection and next-generation matrix $M_{i,j} = (\tau/g) B_{j,i} S_i / n_i$), <https://doi.org/10.1371/journal.pcbi.1002425>, PMCID PMC3297563.
- P. van den Driessche and J. Watmough, "Reproduction numbers and sub-threshold endemic equilibria for compartmental models of disease transmission", Mathematical Biosciences 180 (2002) 29–48, <https://doi.org/10.1016/S0025-5564(02)00108-6>.
