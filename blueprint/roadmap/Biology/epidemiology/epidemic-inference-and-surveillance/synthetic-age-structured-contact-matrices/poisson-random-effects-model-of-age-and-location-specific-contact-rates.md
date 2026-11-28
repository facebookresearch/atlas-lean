# Poisson random-effects model of age- and location-specific contact rates

In a contact survey, let $X^{L}_{i,\alpha}$ be the number of contacts that participant $i$, of age group $a_i$, reports at location $L \in \{\text{home}, \text{work}, \text{school}, \text{other}\}$ with individuals of age group $\alpha$. The model is

$$X^{L}_{i,\alpha} \sim \mathrm{Poisson}\bigl(\sigma_i \, \lambda^{L}_{a_i, \alpha}\bigr),$$

independently given the parameters, where $\sigma_i > 0$ is a participant-level random effect for overall social activity, shared across that participant's locations, and $\lambda^{L}_{a,\alpha}$ is the daily contact rate between age groups $a$ and $\alpha$ at location $L$, the key estimand, with a smoothness prior linking successive age groups. The location-specific matrices $C^{L} = (\lambda^{L}_{a,\alpha})$ are combined into the all-locations matrix

$$C = C^{\text{home}} + C^{\text{work}} + C^{\text{school}} + C^{\text{other}},$$

and are projected to countries without surveys by re-weighting with local population, household, labour-force and school-enrolment age structures. A physical-distancing intervention that reduces transmission outside the household by a fraction $f \in [0,1]$ replaces $C$ by $C^{\text{home}} + (1 - f)\bigl(C^{\text{work}} + C^{\text{school}} + C^{\text{other}}\bigr)$ in an age-structured transmission model, whose next-generation matrix is proportional to the contact matrix times age-specific susceptibility and infectiousness.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Without the random effect, repeated reports by the same participant at several locations would be treated as independent and over-dispersion across individuals would be absorbed into the age rates; the multiplicative $\sigma_i$ turns the Poisson into a Poisson mixture whose marginal variance exceeds its mean, while leaving $\lambda$ interpretable as the rate for an average participant. Because $R_0$ is the spectral radius of a matrix that scales linearly with $C$, a uniform reduction of all contacts by $f$ scales $R_0$ by $1 - f$, but a reduction confined to non-household settings reduces $R_0$ by less, by an amount that depends on how much of the dominant eigenvector's mass sits in household contacts. Comparison of the updated synthetic matrices with empirical matrices from eleven settings gave a median correlation of 0.84 (interquartile range 0.76–0.88), and the basic reproduction number computed from urban matrices exceeded that from rural matrices.

## Sources

- Prem K, van Zandvoort K, Klepac P, Eggo RM, Davies NG, et al. Projecting contact matrices in 177 geographical regions: an update and comparison with empirical data for the COVID-19 era. *PLoS Computational Biology* (2021), Materials and methods, "Updating country-specific demography and setting parameters" and "Impact on modelling of interventions". DOI <https://doi.org/10.1371/journal.pcbi.1009098>. PMCID PMC8354454.
