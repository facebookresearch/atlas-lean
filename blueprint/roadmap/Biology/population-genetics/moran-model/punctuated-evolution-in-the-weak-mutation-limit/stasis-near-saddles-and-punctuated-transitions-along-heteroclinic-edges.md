# Stasis near saddles and punctuated transitions along heteroclinic edges

**Setting.** Consider the competitive-exclusion system $\dot x_i=b_i(x)=x_i(f_i-\bar f(x))$ on the simplex $\Delta_I$ spanned by the pure-type vertices $e^{(k)}$, with distinct fitnesses $f_i>0$, as the deterministic limit of a Moran population of size $N$ whose individuals mutate at rate $\lambda$ along the edges of a mutation graph on types.

**Statement.**

1. *Every vertex is a hyperbolic saddle.* At $e^{(k)}$ the linearization has, for each $i\ne k$, the eigenvalue $f_i-f_k$ with eigenvector $e^{(i)}-e^{(k)}$ along the simplex edge (plus the transversal eigenvalue $-f_k$, irrelevant on $\Delta_I$). So $e^{(k)}$ is attracting along every edge toward a less fit type and repelling along every edge toward a fitter type; its index (number of negative eigenvalues on $\Delta_I$) is the number of types less fit than $k$, and only the fittest vertex is a sink.
2. *Heteroclinic network.* Each edge $[e^{(i)},e^{(k)}]$ is invariant and is a heteroclinic orbit between the two saddles, on which $\dot x_i=(f_i-f_k)x_i(1-x_i)$, a logistic sweep in time of order $\ln N/|f_i-f_k|$ from frequency $1/N$.
3. *Weak-mutation regime.* Let $s$ be the selection coefficient of the current sweep, $M$ the number of beneficial mutations available and $L$ the number of deleterious ones. If

$$r_N=\frac{\lambda N\ln N}{s}\ll1\qquad\text{and}\qquad \frac{\lambda L\ln N}{s}\ll1,$$

then the probability that a further beneficial mutation arises during a sweep is at most $1-e^{-Mr_N}\le Mr_N$, and deleterious mutants produced during a sweep form an asymptotically negligible fraction of the population.

Consequently the population waits near a monomorphic saddle for a time of order $(M\lambda N)^{-1}$ (stasis under purifying selection), then crosses to the next saddle along a heteroclinic edge in time of order $\ln N/s$: punctuated-equilibrium-like dynamics emerge without any criticality assumption.

## Expansion

The Jacobian entries at $e^{(k)}$ are $\partial_kb_k=-f_k$, $\partial_ib_k=-f_i$ and $\partial_ib_i=f_i-f_k$ for $i\ne k$, with all other entries zero, which gives the eigenpairs directly. Restricting to two types gives the logistic edge flow. For the timing claims, a beneficial mutant appears at rate about $M\lambda N$ in a monomorphic population, fixes with probability bounded below (by the survival bound of the fluid-limit theorem) and, when it fixes, does so in $\ln N/s$; the Poisson count of mutations during that window gives the bound $Mr_N$, and deleterious mutants number at most about $\lambda LN\ln N/s\ll N$.

## Depends on

- [Fluid limit and logarithmic fixation time in the multitype Moran model](fluid-limit-and-logarithmic-fixation-time-in-the-multitype-moran-model.md)
- [Weak-mutation limit justifies the origination-fixation chain](../../../molecular-evolution/origination-fixation-dynamics/weak-mutation-limit-justifies-the-origination-fi.md)
- [Rest point of the replicator equation](../../../population-dynamics/replicator-dynamics/is-rest-point.md)

## Sources

- Bakhtin Y, Katsnelson MI, Wolf YI, Koonin EV. Evolution in the weak-mutation limit: Stasis periods punctuated by fast transitions between saddle points on the fitness landscape. *Proc. Natl. Acad. Sci. USA* 118 (2021). <https://doi.org/10.1073/pnas.2015665118> (PMCID: PMC7848522). Section "Heteroclinic Network" and Eqs. (6)-(7).
