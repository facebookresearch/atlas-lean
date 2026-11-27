# Well-posedness and disease-free threshold of the immune-status-structured SIRS model

**Model.** Immune hosts carry a continuous immune status $z \in [z_m, z_M]$ with density $r(t,z)$; immunity wanes deterministically at speed $g(z) > 0$ and is boosted by contact with infectives. With susceptibles $S$, infectives $I$ and total population $N = S + I + \int r\,dz$,

$$S' = b(N) - \beta\frac{SI}{N} - dS + g(z_m)\,r(t,z_m), \qquad I' = \beta\frac{SI}{N} - (\gamma + d + d_I)\,I,$$

$$\partial_t r - \partial_z\big(g(z)\,r\big) = -d\,r + \beta\frac{I}{N}\Big(\int_{z_m}^{z} p(z,v)\,r(t,v)\,dv - r(t,z)\Big),$$

with boundary condition at maximal immunity

$$g(z_M)\,r(t,z_M) = \gamma I + \beta\frac{I}{N}\int_{z_m}^{z_M} p(z_M,v)\,r(t,v)\,dv.$$

Here recovered hosts enter at $z_M$, hosts reaching $z_m$ lose immunity and return to $S$, and a boosting contact moves a host from status $v$ to a higher status $z$ with probability density $p(z,v)$. The birth rate $b \in C^1$ is bounded with $b(0) = 0$, and there is $N^* > 0$ with $b(N) > dN$ on $(0,N^*)$, $b(N) < dN$ beyond, and $b'(N^*) < d$.

**Theorem.**

1. (Well-posedness.) For nonnegative initial data $(S^0, I^0, \psi)$ the model has a unique global solution, and the nonnegative cone is positively invariant.
2. (Disease-free equilibrium.) The unique disease-free equilibrium is $(S, I, r) = (N^*, 0, 0)$. With

$$R_0 = \frac{\beta}{\gamma + d + d_I}, \qquad \tilde R_0 = \frac{\beta}{\gamma + d} \ \ge R_0,$$

it is locally stable if $R_0 < 1$, unstable if $R_0 > 1$, and globally asymptotically stable if $\tilde R_0 < 1$ (for a non-lethal disease, $d_I = 0$, the two thresholds coincide).

Choosing $p$ and $g$ appropriately recovers, as special cases, SIRS-type ODE models with finitely many immune classes and boosting, and delay differential equations with a fixed immunity period (when boosting resets the status to $z_M$ and waning is uniform).

## Expansion

The immune equation mixes transport toward lower status with jumps to higher status, so it is not a size-structured model; it is written with $S$ and $I$ as a perturbation of a linear abstract Cauchy problem whose generator (transport plus boundary feedback) generates a positive semigroup, and the nonlinear terms are locally Lipschitz on the state space with $N > 0$. Positivity is proved by comparison with the variant in which boosting always restores maximal immunity, which shares its characteristic curves. At the disease-free state the $I$ equation linearizes to $I' = (\beta - (\gamma + d + d_I))I$, giving the $R_0$ threshold. Globally, $I' = \beta I(S/N - 1/R_0)$ with $S/N < 1$ drives $I$ to zero exponentially; the proof then shows that the immune mass drains back to $S$ and $N \to N^*$, and it is in controlling the population size along the way that the stronger condition $\tilde R_0 < 1$ is used.

## Sources

- Maria Vittoria Barbarossa, Gergely Röst, "Immuno-epidemiology of a population structured by immune status: a mathematical study of waning immunity and immune system boosting", arXiv (2014). Section 2 (model (M1)), Theorems 3.1, 3.2, Section 4 (Propositions 1–2, Theorems 4.1, 4.2), Sections 5–6 (reductions to ODEs and DDEs). <https://doi.org/10.48550/arXiv.1411.3195>. Published version: Journal of Mathematical Biology 71(6-7) (2015), 1737–1770, <https://doi.org/10.1007/s00285-015-0880-5>; locators above refer to the arXiv version.
