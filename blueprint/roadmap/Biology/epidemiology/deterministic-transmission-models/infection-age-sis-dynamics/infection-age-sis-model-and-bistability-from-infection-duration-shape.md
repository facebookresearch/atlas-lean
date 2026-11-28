# Infection-age SIS model and bistability from infection-duration shape

**Setting.** In a closed, well-mixed population with susceptible fraction $S(t)$, let $i(t,a)$ be the density of infected individuals with infection age (time since infection) $a$, so $S=1-\int_0^\infty i(t,a)\,da$. Infectiousness at age $a$ is $\beta(a)\ge0$ with $\beta\in L^1(\mathbb R_+)$, and the duration of infection is a random variable with density $K$; let $\mathcal F(a)=\int_a^\infty K(s)\,ds$ be the probability of still being infected at age $a$, so recovery (back to $S$, with no lasting immunity) occurs at the hazard rate $K/\mathcal F$. New infections are $i(t,0)=\Lambda(t)S(t)$ with force of infection $\Lambda(t)=\int_0^\infty\beta(a)i(t,a)\,da$; equivalently the incidence $x(t)=i(t,0)$ satisfies the nonlinear renewal equation

$$x(t)=\Bigl(1-\int_0^\infty x(t-a)\mathcal F(a)\,da\Bigr)\int_0^\infty\beta(a)\mathcal F(a)\,x(t-a)\,da .$$

**Disease-free state.** Linearizing at $x\equiv0$ gives the Euler-Lotka equation $1=\int_0^\infty e^{-\lambda a}\beta(a)\mathcal F(a)\,da$, which has a unique real root $r$ (the Malthusian parameter) dominating all complex roots. With

$$R_0=\int_0^\infty\beta(a)\mathcal F(a)\,da,$$

$\operatorname{sign}(r)=\operatorname{sign}(R_0-1)$: the disease-free equilibrium is locally stable if $R_0<1$ and unstable if $R_0>1$.

**Endemic state.** If $R_0>1$ there is a unique endemic equilibrium $S^*=1/R_0$, $x^*=(1-1/R_0)/\int_0^\infty\mathcal F(a)\,da$, with characteristic equation

$$1=\frac{1-R_0}{\int_0^\infty\mathcal F}\int_0^\infty e^{-\lambda a}\mathcal F(a)\,da+\frac1{R_0}\int_0^\infty e^{-\lambda a}\beta(a)\mathcal F(a)\,da,$$

so its stability depends on the Laplace transforms of $\mathcal F$ and $\beta\mathcal F$, not on $R_0$ alone.

**Numerical bifurcation results (Section 4).** For gamma-distributed infection durations, the endemic equilibrium can undergo Hopf bifurcations producing stable periodic solutions that coexist with the stable endemic equilibrium (*genuine bistability*); whether this occurs depends on the shape (coefficient of variation) of the duration distribution. Approximating a gamma distribution with non-integer shape by an Erlang distribution (a linear chain of ODE compartments) can create or remove such bistability (*spurious bistability*), whereas a mean- and variance-matching hypoexponential approximation (Theorem 3.1, from earlier work) and pseudospectral discretization of the renewal equation reproduce the true bifurcation structure.

## Expansion

Integrating the age-structured PDE along characteristics expresses $i(t,a)=x(t-a)\mathcal F(a)$, which turns the model into a renewal equation for incidence. Without infection-age dependence (exponential durations, constant $\beta$) the SIS model has a globally stable endemic state; sharply peaked infectious periods act like delays and can destabilize it, so oscillations require low variability in the infectious period. Matching only the mean of the duration (as Erlang chains with rounded shape do) changes the variance and hence the delay structure, which is why model reduction must preserve at least the first two moments.

## Sources

- F. Scarabel, H. Coldwell, T. Cassidy, "Genuine and spurious bistability in a simple epidemic model with waning immunity", *Mathematical Biosciences* 396 (2026), 109671, Sections 2.2-2.4 (renewal formulation, $R_0$, endemic equilibrium and characteristic equations), Theorem 3.1, Section 4, <https://doi.org/10.1016/j.mbs.2026.109671> (preprint arXiv:2511.09196).
