# Law of large numbers for a Crump–Mode–Jagers epidemic

Consider an individual-based epidemic in which each infected individual $x$, infected at time $\sigma_x$, carries a random life-cycle path $X_x$ through a finite set of compartments and a point process of secondary infections whose intensity in age of infection has density $\tau$ with $\int_0^\infty \tau(a)\,da < \infty$. Infections at time $t$ are thinned by a deterministic contact rate $c(t) \in [0,1]$. The pairs (life cycle, infection process) are i.i.d. across individuals, but within an individual they may be dependent and non-Markovian. Start from $N$ individuals with i.i.d. initial ages of infection drawn from a density $g$, and define the empirical measure of ages and compartments

$$\mu_t^N(da \times \{i\}) = \sum_{\sigma_x < t} \delta_{(t-\sigma_x,\; X_x(t-\sigma_x))}(da \times \{i\}).$$

Then for every $t > 0$, almost surely and in the weak topology,

$$\frac{1}{N}\mu_t^N(da \times \{i\}) \longrightarrow n(t,a)\,p(a,i)\,da \quad (N \to \infty),$$

where $p(a,i) = \mathbb{P}(X(a) = i)$ and $n$ is the weak solution of the linear McKendrick–von Foerster equation

$$\partial_t n + \partial_a n = 0, \qquad n(t,0) = c(t)\int_0^\infty n(t,a)\,\tau(a)\,da, \qquad n(0,a) = g(a).$$

In particular, the number of individuals in compartment $i$ divided by $N$ converges almost surely to $\int_0^\infty n(t,a)\,p(a,i)\,da$.

If instead the process starts from one individual and is supercritical, $\int_0^\infty \tau(a)\,da > 1$, let $\alpha > 0$ solve $\int_0^\infty e^{-\alpha a}\tau(a)\,da = 1$. Conditional on non-extinction, the age structure at a large random time is asymptotically exponential with rate $\alpha$, scaled by a random factor determined by the early infections.

## Depends on

- [Decorated age-of-infection model and compartment counts](decorated-age-of-infection-model-and-compartment-counts.md)
- [Euler–Lotka equation for the reproductive number](../euler-lotka-equation-and-the-reproduction-number/renewal-exp-iff-reproduction-number.md)

## Expansion

The infected population is a Crump–Mode–Jagers branching process with a time-varying thinning $c(t)$. Depletion of susceptibles is ignored, which is why the limit is linear. A forward Feynman–Kac formula identifies the mean of $\mu_t^N/N$ with $n(t,a)p(a,i)$, where $n$ is the unique weak solution of the PDE. Since the $N$ initial lineages are i.i.d., the strong law of large numbers gives almost-sure convergence on a countable convergence-determining class of test functions. In the single-ancestor supercritical case the Malthusian parameter $\alpha$ is the Euler–Lotka root of $\tau$, and the Jagers–Nerman limit theorem gives a stable age distribution proportional to $e^{-\alpha a}$ on the non-extinction event.

## Sources

- F. Foutel-Rodier, F. Blanquart, P. Courau, P. Czuppon, J.-J. Duchamps, J. Gamblin, É. Kerdoncuff, R. Kulathinal, L. Régnier, L. Vuduc, A. Lambert, E. Schertzer, *From individual-based epidemic models to McKendrick–von Foerster PDEs: a guide to modeling and inferring COVID-19 dynamics*, Journal of Mathematical Biology 85 (2022), 43, <https://doi.org/10.1007/s00285-022-01794-4>, PMCID PMC9517997. Theorem 1 (large initial population, Eqs. (4)–(6)) and Theorem 2 (one individual, Eq. (9)); proofs in Section 3.
