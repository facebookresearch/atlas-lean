# Law of large numbers for a Crump–Mode–Jagers epidemic

Consider an individual-based epidemic in which each infected individual $x$, infected at time $\sigma_x$, carries a random life-cycle path $X_x$ through a finite set of compartments and a point process of secondary infections whose intensity in age of infection has density $\tau$ with $\int_0^\infty \tau(a)\,da < \infty$. Infections at time $t$ are thinned by a deterministic contact rate $c(t) \in [0,1]$. The pairs (life cycle, infection process) are i.i.d. across individuals, but within an individual they may be dependent and non-Markovian. Start from $N$ individuals with i.i.d. initial ages of infection drawn from a density $g$, and define the empirical measure of ages and compartments

$$\mu_t^N(da \times \{i\}) = \sum_{\sigma_x < t} \delta_{(t-\sigma_x,\; X_x(t-\sigma_x))}(da \times \{i\}).$$

Then for every $t > 0$, almost surely and in the weak topology,

$$\frac{1}{N}\mu_t^N(da \times \{i\}) \longrightarrow n(t,a)\,p(a,i)\,da \quad (N \to \infty),$$

where $p(a,i) = \mathbb{P}(X(a) = i)$ and $n$ is the weak solution of the linear McKendrick–von Foerster equation

$$\partial_t n + \partial_a n = 0, \qquad n(t,0) = c(t)\int_0^\infty n(t,a)\,\tau(a)\,da, \qquad n(0,a) = g(a).$$

In particular, the number of individuals in compartment $i$ divided by $N$ converges almost surely to $\int_0^\infty n(t,a)\,p(a,i)\,da$.

**Single ancestor (Theorem 2 of the source).** This is a separate statement with its own hypotheses. Suppose the process is supercritical, $\int_0^\infty \tau(a)\,da > 1$, and let $\alpha > 0$ solve $\int_0^\infty e^{-\alpha a}\tau(a)\,da = 1$. Start from a single individual, and let $(t_K)_{K \ge 0}$ be stopping times for the natural filtration of the process with $t_K \to \infty$ on the non-extinction event. There is no thinning before $t_K$: in the $K$-th process the contact rate at time $t$ is $c(t - t_K)$, with $c \equiv 1$ for negative arguments; write $\mu^K_t$ for its empirical measure of ages and compartments. Then, conditional on non-extinction, there is a random variable $W_\infty > 0$ almost surely with

$$e^{-\alpha t_K}\,\#\{x : \sigma_x < t_K\} \longrightarrow W_\infty \quad \text{in probability} \quad (K \to \infty),$$

and for every $t > 0$,

$$e^{-\alpha t_K}\,\mu^K_{t_K + t}(da \times \{i\}) \longrightarrow W_\infty\, n(t, a)\,p(a, i)\,da \quad \text{in probability, for the weak topology,}$$

where $n$ solves the same linear McKendrick–von Foerster equation with the exponential initial profile $g(a) = \alpha e^{-\alpha a}$. The arbitrary thinning of the large-population statement is not allowed before $t_K$: even a constant thinning $c < 1$ would change the growth rate $\alpha$.

## Depends on

- [Decorated age-of-infection model and compartment counts](decorated-age-of-infection-model-and-compartment-counts.md)

## Proof depends on

- [Euler–Lotka equation for the reproductive number](../euler-lotka-equation-and-the-reproduction-number/renewal-exp-iff-reproduction-number.md)

## Expansion

The infected population is a Crump–Mode–Jagers branching process with a time-varying thinning $c(t)$. Depletion of susceptibles is ignored, which is why the limit is linear. A forward Feynman–Kac formula identifies the mean of $\mu_t^N/N$ with $n(t,a)p(a,i)$, where $n$ is the unique weak solution of the PDE. Since the $N$ initial lineages are i.i.d., the strong law of large numbers gives almost-sure convergence on a countable convergence-determining class of test functions. In the single-ancestor case the Malthusian parameter $\alpha$ is the Euler–Lotka root of $\tau$, the unthinned growth up to $t_K$ gives the random factor $W_\infty$ and a stable age distribution proportional to $e^{-\alpha a}$ at time $t_K$, and that exponential density is the initial profile for the linear PDE that describes the population after $t_K$. The source proves this by viewing the population at time $t_K + t$ as a random characteristic of the population at time $t_K$; the convergence is in probability.

## Sources

- F. Foutel-Rodier, F. Blanquart, P. Courau, P. Czuppon, J.-J. Duchamps, J. Gamblin, É. Kerdoncuff, R. Kulathinal, L. Régnier, L. Vuduc, A. Lambert, E. Schertzer, *From individual-based epidemic models to McKendrick–von Foerster PDEs: a guide to modeling and inferring COVID-19 dynamics*, Journal of Mathematical Biology 85 (2022), 43, <https://doi.org/10.1007/s00285-022-01794-4>, PMCID PMC9517997. Theorem 1 (large initial population, Eqs. (4)–(6)) and Theorem 2 (one individual, stopping times $t_K$, convergence in probability); proofs in Section 3.
