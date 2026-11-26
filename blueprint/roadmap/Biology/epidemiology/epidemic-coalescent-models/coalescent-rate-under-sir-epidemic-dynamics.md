# Coalescent rate under SIR epidemic dynamics

Let a pathogen spread in a large host population with prevalence $I(t)$ (number of infected hosts) and incidence $f(t)$ (new infections per unit time), and let $A(t) \ge 2$ sampled lineages be ancestral to a sample at time $t$, with time running backwards from sampling. Each transmission event links an infector and an infectee; it merges two sampled lineages exactly when both hosts involved carry sampled lineages. Choosing the pair uniformly among infected hosts gives the coalescence rate

$$\lambda_A(t) = f(t)\, \frac{\binom{A}{2}}{\binom{I(t)}{2}} \approx \binom{A}{2} \frac{2 f(t)}{I(t)^2} \qquad (I(t) \gg 1).$$

For the SIR model with susceptible fraction $S(t)$, transmission rate $\beta$ per infected host and recovery rate $\gamma$, the incidence is $f = \beta S I$ and

$$\lambda_A(t) = \binom{A}{2} \frac{2\beta S(t)}{I(t)}.$$

Properties:

- the rate equals the Kingman rate $\binom{A}{2}/N_e(t)$ with $N_e(t) = I(t) / (2\beta S(t))$, so the genealogy is a time-changed Kingman coalescent;
- early in an epidemic ($S \approx 1$), $N_e(t) = I(t)/(2\beta)$: effective population sizes estimated with the Kingman coalescent are proportional to prevalence during exponential growth;
- for exponential growth $N(t) = N_0 e^{-rt}$ ($t$ measured backwards), the rate $\binom{A}{2} e^{rt}/N_0$ is small near the sampling time, so external branches are long relative to branches near the root (star-like trees);
- combined with an exponentially distributed infectious period of mean $D$, a growth rate $r$ estimated from the genealogy gives the basic reproduction number $R_0 = 1 + rD$.

## Depends on

- [Kingman's coalescent](../../coalescent-theory/coalescents/merger-rate-dirac-zero.md)
- [Solution of the Kermack–McKendrick SIR system](../kermack-mckendrick-sir-model/is-solution.md)
- [Exponential generation interval](../euler-lotka-equation-and-the-reproduction-number/reproduction-number-exp-measure.md)

## Expansion

The factor $\binom{A}{2}/\binom{I}{2}$ is the probability that two hosts chosen at random from the $I$ infected both carry one of the $A$ sampled lineages; transmissions occur at the incidence rate $f$, so coalescences occur at the product. Compared with the constant-size Kingman coalescent, the SIR rate is damped by the susceptible fraction $S(t)$, which separates prevalence from effective size once depletion of susceptibles matters. This is the basis for fitting epidemic models directly to dated phylogenies; an early application estimated $R_0$ of pandemic 2009 influenza from 11 hemagglutinin sequences and the infectious period.

## Sources

- E. M. Volz, K. Koelle, T. Bedford, "Viral phylodynamics", PLoS Computational Biology 9(3) (2013) e1002947, Methods, "Coalescent Theory and Phylodynamics", subsections "Effective population size" and "Compartmental models", <https://doi.org/10.1371/journal.pcbi.1002947> (PMC3605911).
