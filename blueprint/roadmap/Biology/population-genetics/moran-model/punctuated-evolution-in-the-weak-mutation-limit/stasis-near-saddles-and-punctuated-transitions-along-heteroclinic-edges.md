# Stasis near saddles and punctuated transitions along heteroclinic edges

**Setting.** Consider the competitive-exclusion system $\dot x_i=b_i(x)=x_i(f_i-\bar f(x))$ on the simplex $\Delta_I$ spanned by the pure-type vertices $e^{(k)}$, with distinct fitnesses $f_i>0$, as the deterministic limit of a Moran population of size $N$ whose individuals mutate at rate $\lambda$ along the edges of a mutation graph on types.

**Statement.**

1. *Every vertex is a hyperbolic saddle.* At $e^{(k)}$ the linearization has, for each $i\ne k$, the eigenvalue $f_i-f_k$ with eigenvector $e^{(i)}-e^{(k)}$ along the simplex edge (plus the transversal eigenvalue $-f_k$, irrelevant on $\Delta_I$). So $e^{(k)}$ is attracting along every edge toward a less fit type and repelling along every edge toward a fitter type; its index (number of negative eigenvalues on $\Delta_I$) is the number of types less fit than $k$, and only the fittest vertex is a sink.
2. *Heteroclinic network.* Each edge $[e^{(i)},e^{(k)}]$ is invariant and is a heteroclinic orbit between the two saddles, on which $\dot x_i=(f_i-f_k)x_i(1-x_i)$, a logistic sweep: the fitter type's odds $x/(1-x)$ grow like $e^{|f_i-f_k|t}$, so the deterministic passage from frequency $1/N$ to $1-1/N$ takes time $2\ln(N-1)/|f_i-f_k|$.
3. *Weak-mutation regime.* Let $s$ be the selection coefficient of the current sweep, $M$ the number of beneficial mutations available and $L$ the number of deleterious ones. If

$$r_N=\frac{\lambda N\ln N}{s}\ll1\qquad\text{and}\qquad \frac{\lambda L\ln N}{s}\ll1,$$

then, over a sweep window of length $2\ln N/s$ (the deterministic passage from one copy to fixation), the probability that a further beneficial mutation arises is at most $1-e^{-2Mr_N}\le 2Mr_N$, and deleterious mutants produced during the window, at most about $2\lambda LN\ln N/s\ll N$ of them, form an asymptotically negligible fraction of the population.

Consequently the population waits near a monomorphic saddle for a time of order $(M\lambda N)^{-1}$ (stasis under purifying selection), then crosses to the next saddle along a heteroclinic edge in time about $2\ln N/s$: punctuated-equilibrium-like dynamics emerge without any criticality assumption.

## Expansion

The Jacobian entries at $e^{(k)}$ are $\partial_kb_k=-f_k$, $\partial_ib_k=-f_i$ and $\partial_ib_i=f_i-f_k$ for $i\ne k$, with all other entries zero, which gives the eigenpairs directly. Restricting to two types gives the logistic edge flow. For the timing claims, a beneficial mutant appears at rate about $M\lambda N$ in a monomorphic population, fixes with probability bounded below (by the survival bound of the fluid-limit theorem) and, when it fixes, does so in about $2\ln N/s$; beneficial mutations arise at total rate at most $M\lambda N$, so the Poisson count during that window is zero with probability at least $e^{-2M\lambda N\ln N/s}=e^{-2Mr_N}$, and deleterious mutants number at most about $2\lambda LN\ln N/s\ll N$.

(The source's Eq. (6) bounds the probability of a beneficial mutation during the sweep by $1-e^{-MN\lambda C\ln N}=1-e^{-Mr_N}\le Mr_N$, using a sweep time $C\ln N$ with $C=1/s$. A mutant starting as one copy needs time about $2\ln N/s$ to fix, not $\ln N/s$: about $\ln N/s$ to grow from $1/N$ to a constant fraction and another $\ln N/s$ to reduce the resident from a constant fraction to $1/N$, as the logistic odds $(N-1)^{-1}e^{st}$ show. So the window doubles and the bound is $2Mr_N$; the source's deleterious count $\lambda LN\ln N/s$ for $t=\ln N/s$ doubles in the same way. The conditions $r_N\ll1$ and $\lambda L\ln N/s\ll1$ are unchanged, so the qualitative conclusion stands.)

## Depends on

- [Fluid limit and logarithmic fixation time in the multitype Moran model](fluid-limit-and-logarithmic-fixation-time-in-the-multitype-moran-model.md)
- [Weak-mutation limit justifies the origination-fixation chain](../../../molecular-evolution/origination-fixation-dynamics/weak-mutation-limit-justifies-the-origination-fi.md)
- [Rest point of the replicator equation](../../../population-dynamics/replicator-dynamics/is-rest-point.md)

## Sources

- Bakhtin Y, Katsnelson MI, Wolf YI, Koonin EV. Evolution in the weak-mutation limit: Stasis periods punctuated by fast transitions between saddle points on the fitness landscape. *Proc. Natl. Acad. Sci. USA* 118 (2021). <https://doi.org/10.1073/pnas.2015665118> (PMCID: PMC7848522). Section "Heteroclinic Network" and Eqs. (6)-(7).
