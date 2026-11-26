# Two-variant logistic replacement and the selection coefficient

Let an epidemic carry two variants of a pathogen. Suppose the number infected with the wild-type variant grows exponentially at rate $r$ and the number infected with the derived variant grows at rate $r(1 + s)$, where $s$ is the **selection coefficient** (the proportional increase in the epidemic growth rate). Writing $N_D$ and $N_G$ for the numbers infected at time $0$, the derived variant's frequency at time $t$ is

$$f_G(t) = \frac{N_G\, e^{r(1+s)t}}{N_G\, e^{r(1+s)t} + N_D\, e^{rt}} = \frac{1}{1 + (N_D/N_G)\,e^{-\rho t}}, \qquad \rho := r s,$$

a logistic curve in $t$ with rate $\rho$. If sequenced specimens are sampled in proportion to the prevalence of each variant, genotypes $y_1, \dots, y_n$ observed at times $t_1, \dots, t_n$ have log-likelihood

$$\ell(\rho, f_G(t_0)) = \sum_{i=1}^{n}\Bigl[\mathbf 1\{y_i = G\}\log f_G(t_i) + \bigl(1 - \mathbf 1\{y_i = G\}\bigr)\log\bigl(1 - f_G(t_i)\bigr)\Bigr],$$

which is the likelihood of a logistic regression of genotype on sampling time. **Only the product $\rho = rs$ is identified from frequency data.** Converting $\hat\rho$ into a selection coefficient requires the epidemic growth rate $r$ from outside this model, for instance $r = (R_0 - 1)/\tau$ for a reproduction number $R_0$ and a serial interval $\tau$; the interval for $s$ must then combine the profile-likelihood interval for $\rho$ with the plausible range of $r$. The same formula applies during epidemic decline, where $r < 0$.

## Depends on

- [Logistic growth equation](../population-dynamics/logistic-growth-equation/logistic.md)
- [Log-odds grow linearly](../population-dynamics/logistic-growth-equation/logit-logistic.md)

## Expansion

Dividing numerator and denominator by $N_G e^{r(1+s)t}$ gives the stated logistic form with log-odds $\log(f_G/(1 - f_G)) = \log(N_G/N_D) + \rho t$ linear in time, so the model is exactly a logistic regression with time as the single covariate. The derivation assumes both variants grow exponentially with a common factor $r$ over the observation window, and that sampling probability does not depend on genotype. Differential sampling, structured transmission, repeated introductions from outside the population, and founder effects break it; restricting the analysis to clusters whose first detection predates the window controls the introduction problem. Because $\rho = rs$, two distinct growth phases with different $r$ but the same $s$ give different logistic slopes, which is a consistency check: here the growth and the decline phase gave compatible estimates ($\hat s \approx 0.21$ and $0.27$). Independent phylodynamic estimates (parametric boom-bust and non-parametric coalescent models, and a structured SEIR coalescent) estimate $s$ from the genealogies instead, with much wider intervals.

## Sources

- E. Volz, V. Hill, J. T. McCrone et al. (COG-UK Consortium), "Evaluating the effects of SARS-CoV-2 spike mutation D614G on transmissibility and pathogenicity", Cell 184 (2021), 64–75 (online 2020), Methods ("Logistic growth model") and Results (Table 1, "Parametric phylodynamic analysis"), <https://doi.org/10.1016/j.cell.2020.11.020>, PMCID PMC7674007.
