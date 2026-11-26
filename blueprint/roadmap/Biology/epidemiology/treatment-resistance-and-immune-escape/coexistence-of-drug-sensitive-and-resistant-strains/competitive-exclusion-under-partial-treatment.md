# Competitive exclusion of drug-sensitive and resistant strains under partial treatment

Consider a well-mixed population in which a drug-sensitive (wild-type) and a drug-resistant strain spread by SIS dynamics with no co-infection or super-infection. Infected individuals transmit at rate $\kappa > 0$ and recover to susceptibility at rate $g > 0$. A fraction $f \in [0, 1]$ of individuals is treated whenever infected; treatment multiplies the transmission of the sensitive strain by $1 - \epsilon$ ($0 < \epsilon < 1$) and does not affect the resistant strain, which instead pays a transmission cost $c \in (0, 1)$. With $w_u, w_t, r_u, r_t$ the proportions of the population infected with the sensitive or resistant strain and untreated or treated,

$$\dot w_u = \kappa\big(w_u + (1-\epsilon) w_t\big)\big((1-f) - w_u - r_u\big) - g w_u, \qquad \dot w_t = \kappa\big(w_u + (1-\epsilon) w_t\big)\big(f - w_t - r_t\big) - g w_t,$$

$$\dot r_u = \kappa (1-c)(r_u + r_t)\big((1-f) - w_u - r_u\big) - g r_u, \qquad \dot r_t = \kappa (1-c)(r_u + r_t)\big(f - w_t - r_t\big) - g r_t.$$

The strain-specific basic reproductive numbers are

$$R_0^{w} = \frac{\kappa (1 - \epsilon f)}{g}, \qquad R_0^{r} = \frac{\kappa (1 - c)}{g}.$$

If both are below one, only the infection-free equilibrium persists. Otherwise only the strain with the larger $R_0$ persists, at total prevalence $1 - 1/R_0$, and the other goes extinct. In particular the resistant strain takes over if and only if $\epsilon f > c$: partial treatment coverage alone never allows stable coexistence in an unstructured population.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [A singular real 2 × 2 matrix has exactly the eigenvalues 0 and tr M](../../../../Analysis/partial-differential-equations/bifurcation-of-turing-pattern-branches/exists-eigenvector-iff-of-det-eq-zero.md)
- [Basic reproduction number of the SIS model](../../sis-epidemic-model/r0-eq.md)
- [Endemic limit of every SIS solution](../../sis-epidemic-model/tendsto-infected-endemic.md)

## Proof sketch

At the infection-free state the sensitive strain's next-generation matrix is $\frac{\kappa}{g}\begin{pmatrix} 1-f & (1-f)(1-\epsilon) \\ f & f(1-\epsilon) \end{pmatrix}$. It has rank one, so its spectral radius is its trace, $\kappa(1 - \epsilon f)/g$, the average transmission over treated and untreated infections. The resistant strain is unaffected by treatment, so its matrix has spectral radius $\kappa(1-c)/g$. Comparing the two gives the criterion $\epsilon f > c$. Both strains compete for a single pool of susceptibles that mixes over treatment status, so the model behaves like a one-resource competition with exclusion of the weaker strain. The model is structurally neutral: with $\epsilon = c = 0$ the two strains are identical and persist at whatever proportions they start at. The same exclusion holds if treatment instead speeds recovery, $g \to g + \tau$. Real surveillance data show long-term intermediate resistance frequencies, which this exclusion result cannot reproduce; this motivates structured-population versions of the model.

## Sources

- M. S. Krieger, C. E. Denison, T. L. Anderson, M. A. Nowak and A. L. Hill, "Population structure across scales facilitates coexistence and spatial heterogeneity of antibiotic-resistant infections", PLoS Computational Biology 16 (2020) e1008010, Results ("Absence of coexistence in an unstructured population", Figure 3A–C) and Methods ("Model equations", Equation 1), <https://doi.org/10.1371/journal.pcbi.1008010>, PMCID: PMC7365476.
