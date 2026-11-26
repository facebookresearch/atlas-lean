# Cumulative hazard model of infection prevalence by age

Let $\lambda : \mathbb{R} \to [0,\infty)$ be a locally integrable **annual hazard of infection** (the force of infection, per person-year) acting on every uninfected individual in a population at calendar time $u$. Assume that (i) everyone is uninfected at birth, (ii) infection is lifelong (no clearance), and (iii) mortality and migration do not depend on infection status. Write

$$H(s,t) = \int_s^t \lambda(u)\,du$$

for the cumulative hazard over $[s,t]$. For a person of age $a \ge 0$ at time $T$ (born at $T-a$), the probability of having ever been infected is

$$P(a,T) = 1 - \exp\big(-H(T-a,\,T)\big).$$

If $N(a,T)$ is the population of age $a$ at time $T$, the population prevalence is $\pi(T) = \int P(a,T)\,N(a,T)\,da \big/ \int N(a,T)\,da$ (a sum over single-year age groups in practice).

**Proposition.**

1. For fixed $T$, $a \mapsto P(a,T)$ is nondecreasing, and strictly increasing on any age range over which $\lambda$ is positive on a set of positive measure.
2. If $\lambda \equiv \lambda_0$ is constant, $P(a,T) = 1 - e^{-\lambda_0 a}$, and $\lambda_0 = -\ln\big(1 - P(a,T)\big)/a$ for every $a > 0$.
3. The annual risk of infection $r(u)$ in a year of constant hazard $\lambda(u)$ is $r = 1 - e^{-\lambda}$, so $r \approx \lambda$ when $\lambda$ is small.

## Expansion

Survival of the uninfected state is a time-inhomogeneous pure death process with rate $\lambda(u)$, so the probability of escaping infection from birth to time $T$ is $\exp(-H(T-a,T))$. Monotonicity in age holds because older cohorts have been exposed over a superset of calendar years. Part 2 is the classical inversion used to estimate a (constant) annual risk of infection from a tuberculin skin test survey of children of mean age $a$. In the global re-estimation of latent tuberculosis, the hazard was reconstructed per country for 1934–2014 by Gaussian-process regression (with a linear trend, on a log scale) through survey-based estimates and through estimates derived from smear-positive prevalence via the revised Styblo ratio; 200 sampled trajectories per country were pushed through this formula and combined with 2014 demography. This produced a global prevalence of about 23% (about 1.7 billion people) in 2014, rising with age in every region.

## Sources

- R. M. G. J. Houben and P. J. Dodd, "The global burden of latent tuberculosis infection: a re-estimation using mathematical modelling", PLoS Medicine 13 (2016) e1002152, Methods (cumulative hazard of infection by age) and Results ("LTBI Prevalence on Global, Regional, and Country Level", "Age Trends"), <https://doi.org/10.1371/journal.pmed.1002152>, PMCID PMC5079585.
