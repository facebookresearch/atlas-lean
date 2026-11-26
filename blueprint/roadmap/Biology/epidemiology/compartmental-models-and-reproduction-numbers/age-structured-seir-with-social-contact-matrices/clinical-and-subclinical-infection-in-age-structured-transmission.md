# Clinical and subclinical infection in age-structured transmission

**Model.** In an age-structured SEIR-type model with age groups $i = 1, \dots, n$, infected individuals pass through a latent stage (mean duration $d_E$) and then, with age-dependent probability $y_i$, a preclinical infectious stage (mean $d_P$) followed by a clinical infectious stage (mean $d_C$), or, with probability $1 - y_i$, a subclinical infectious stage (mean $d_S$). Preclinical and clinical individuals have infectiousness $1$ (clinical infectiousness may be scaled by $\kappa_C \in [0,1]$ to represent self-isolation of symptomatic cases), and subclinical individuals have relative infectiousness $f \in [0,1]$. Contacts are summed over settings,

$$C = \sum_{s \in \{\text{home},\,\text{work},\,\text{school},\,\text{other}\}} w_s\, C^{(s)},$$

where $C^{(s)}_{ij}$ is the mean number of daily contacts that a person in group $i$ has with group $j$ in setting $s$ and $w_s \in [0,1]$ is the fraction of setting-$s$ contacts kept under an intervention (for example $w_{\text{school}} = 0$ for school closures). Susceptibility per contact is a common constant $u$.

**Proposition.** The next-generation matrix of this model at a fully susceptible population is

$$K_{ij} = u\, C_{ij}\, \big[\, y_j\,(d_P + \kappa_C\, d_C) + (1 - y_j)\, f\, d_S \,\big],$$

the expected number of infections in group $i$ caused by one infected person in group $j$, and $R_0 = \rho(K)$. Consequently:

1. $R_0$ is linear in $u$, so $u$ can be calibrated to any target $R_0$ for a given contact structure.
2. An intervention that multiplies setting weights $w_s$ and the clinical infectiousness $\kappa_C$ changes $R_0$ to $\rho(K')$, with $K'$ built from the modified $C$ and $\kappa_C$; because $K$ has nonnegative entries, lowering any $w_s$ or $\kappa_C$ cannot increase $R_0$.
3. Self-isolation of symptomatic cases removes at most the clinical-stage term $u\,C_{ij}\,y_j\,d_C$: preclinical and subclinical transmission, which is large in age groups with small $y_j$ (children), is unaffected.

## Depends on

- [Next-generation matrix of an age-structured SEIR model](next-generation-matrix-of-an-age-structured-seir-model.md)

## Expansion

An infected person in group $j$ spends expected time $y_j(d_P + d_C)$ in clinical-pathway infectious stages and $(1 - y_j)d_S$ in the subclinical stage, during which they meet $C_{ij}$ members of group $i$ per day, each infected with probability $u$ per contact (per day of infectiousness, scaled by the relative infectiousness of the stage). Summing gives $K_{ij}$; the latent stage only delays transmission. Monotonicity in property 2 follows from the Perron–Frobenius theorem: the spectral radius of a nonnegative matrix is nondecreasing in each entry. The age dependence of $y_j$ is what makes children contribute mainly through subclinical transmission, which is why school closures and symptom-based isolation have different leverage on $R_0$.

## Sources

- Davies NG, Kucharski AJ, Eggo RM, Gimma A, Edmunds WJ, and the CMMID COVID-19 working group, "Effects of non-pharmaceutical interventions on COVID-19 cases, deaths, and demand for hospital services in the UK: a modelling study" (2020), Methods (model structure: latent, preclinical, clinical and subclinical stages with mean durations 4, 1.5, 3.5 and 5 days, subclinical infectiousness 50%; setting-specific contact matrices scaled by interventions), <https://doi.org/10.1016/s2468-2667(20)30133-x>, PMCID PMC7266572.
