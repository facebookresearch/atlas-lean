# Local stability of the disease-free state under nonlinear subunit templating

**Template-assistance model.** Normal monomers $V$ are converted into misfolded subunits $S$ by templating at rate $\rho V f(S)$ with a templating function $f \ge 0$, subunits revert at rate $\omega$ and are degraded at rate $\delta$; aggregates (number $U$, mass $P$, nucleus size $x_0$, fragmentation rate $\beta$, clearance rate $\mu$) polymerize subunits at rate $\tau$. The single-strain system (9), as encoded by its Jacobian, is

$$\dot V = \lambda - \gamma V - \rho V f(S) + \omega S, \qquad \dot S = \rho V f(S) - (\omega + \delta) S - \tau S U + \beta x_0^2 U,$$

$$\dot U = \beta P - (\mu + 2\beta x_0) U, \qquad \dot P = \tau S U - \beta x_0^2 U - \mu P,$$

with all rate constants positive. Solutions starting in $X = \{V, S, U, P - x_0 U \ge 0\}$ exist, are unique and stay in $X$ (Lemma 1).

**Proposition 1.** The disease-free equilibrium $(V, S, U, P) = (\lambda/\gamma, 0, 0, 0)$ exists for all positive parameters and is locally asymptotically stable iff

$$\frac{\lambda}{\gamma} f'(0) < \frac{\omega + \delta}{\rho}.$$

In particular, if $f'(0) = 0$ (as for $f(S) = S^2/(K + S)$), the disease-free equilibrium is locally stable for every choice of positive parameters, and so can be stable together with endemic equilibria.

## Depends on

- [Competitive exclusion of prion strains in the nucleated polymerization model](competitive-exclusion-in-the-multistrain-nucleated-polymerization-model.md)

## Expansion

At the disease-free state the Jacobian is block triangular with eigenvalues $-\gamma$, two eigenvalues of the aggregate block that are negative, and $\rho(\lambda/\gamma) f'(0) - \omega - \delta$, the linear growth rate of a small subunit population. A templating rate that is superlinear near zero makes that eigenvalue $-(\omega + \delta) < 0$ regardless of the other parameters, so small inocula die out while large ones can establish: infection outcome depends on the inoculum. With a linear templating rate this co-stability disappears. In the multistrain version each strain has its own subunit species, so strains no longer compete directly for the same polymerization substrate, which is what lets several strains coexist stably over wide parameter ranges, unlike the classical model.

## Sources

- P. Lemarre, L. Pujo-Menjouet, S. S. Sindi, "Generalizing a mathematical model of prion aggregation allows strain coexistence and co-stability by including a novel misfolded species", Journal of Mathematical Biology 78 (2019) 465–495, Section 3, System (9), Lemma 1, Proposition 1, <https://doi.org/10.1007/s00285-018-1280-4> (PMC6399074).
