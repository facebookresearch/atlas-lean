# Stochastic SIRS with varying infectivity and random pulse vaccination

**Individual-based model.** A population of $N$ individuals. Individual $k$ carries i.i.d. random **infectivity** and **susceptibility** functions: $(\lambda^I_{k,0},\gamma^I_{k,0})$ until its first infection after time 0, then fresh copies $(\lambda^I_{k,i},\gamma^I_{k,i})$ of $(\lambda^I,\gamma^I)$ after its $i$-th infection (functions of time since that infection), with $0\le\gamma\le1$ and $\lambda\le\lambda_*<\infty$; susceptibility can recover gradually (waning immunity), and $\eta=\sup\{t:\lambda^I(t)>0\}$ is the infectious period. Vaccination campaigns occur for each individual at the jump times of a Poisson random measure with arbitrary $\sigma$-finite intensity $\nu$ on $\mathbb R_+$; after the $j$-th vaccination susceptibility follows a random function $\gamma^V$ (possibly waning, so immunity need not be permanent), and vaccination acts only on individuals who are not currently infectious. Infection pressure on an individual is its current susceptibility times the population mean infectivity.

**Theorem (functional law of large numbers).** Let $\mathfrak S^N(t)$ be the average susceptibility and $\mathfrak F^N(t)$ the total force of infection (average infectivity). The system of nonlinear Volterra-type integral equations for $(x,y)=(\mathfrak S,\mathfrak F)$, in which each term averages $\gamma$ or $\lambda$ over infection histories weighted by survival factors $\exp(-\int\gamma(r)y(r)dr)$ and by the probability $e^{-\nu((a,b])}$ of no vaccination during an interval, has a unique solution in $D(\mathbb R_+,\mathbb R_+)^2$, and

$$(\mathfrak S^N,\mathfrak F^N)\ \xrightarrow[N\to\infty]{\ \mathbb P\ }\ (\mathfrak S,\mathfrak F)\quad\text{in }D^2,$$

with explicit formulas for the limiting compartment proportions in terms of $(\mathfrak S,\mathfrak F)$. For deterministic infection periods and constant rates it reduces to classical pulse-vaccination ODE models.

**Theorem (long-time behavior).** Let $R_0=\int_0^\infty\bar\lambda(s)\,ds$, $\bar\lambda=\mathbb E\lambda^I$, and $\gamma^I_*=\sup_t\gamma^I(t)\le1$. If infectivity ends before susceptibility returns and $\eta$ is integrable, then
1. if $R_0<1$, $\mathfrak F(t)\to0$ (the infection-free solution is globally attracting, with $\int_0^\infty\mathfrak F<\infty$);
2. without vaccine waning ($\gamma^V\equiv0$), the same holds under the weaker condition $R_0<\mathbb E[1/\gamma^I_*]$, the reciprocal of the harmonic mean of maximal susceptibility, a threshold that is sharp for some non-Markovian models and for the classical ODE model;
3. conversely, with $\gamma_*=\min(\gamma^I_*,\gamma^V_*)$ deterministic and positive, monotone susceptibilities and a regularity condition on $\bar\lambda$, if $R_0>\mathbb E[1/\gamma_*]$ and $\mathfrak F(0)>0$ then $\liminf_{t\to\infty}\mathfrak F(t)>0$: the disease persists.

If campaigns accumulate ($\nu([0,t])\to\infty$) with permanent vaccine immunity, the susceptible mass tends to zero below threshold.

## Depends on

- [Kermack-McKendrick SIR model](../kermack-mckendrick-sir-model/README.md)

## Expansion

The proof builds the limit through a Poisson-measure calculus: for a Poisson random measure $Q$ with intensity $\nu$ and an independent predictable $\varphi$, $\mathbb E\big[\exp(-\int_\tau^t\varphi(r)\mathbb 1_{Q((\tau,r])=0}dr)\big]$ is expressed through the law of the first campaign after $\tau$, $\mathbb P(T_\tau\le s)=1-e^{-\nu((\tau,s])}$, which produces the $e^{-\nu}$ factors in the limit equations. A coupling of the $N$-particle system with i.i.d. copies driven by the deterministic limit force of infection, plus Gronwall-type bounds on the number of reinfections, gives convergence in probability. Below threshold a renewal-type inequality $\mathfrak F\le(\text{decaying initial term})+R_0\sup\mathfrak F$ forces extinction; using maximal susceptibility improves $1$ to $\mathbb E[1/\gamma^I_*]$ because reinfected individuals are only partially susceptible. Persistence above threshold uses lower bounds on susceptibility recovery and a contradiction argument on the long-run force of infection.

## Sources

- A. B. Zotsa Ngoufack, "Stochastic epidemic models with pulse vaccination, varying infectivity and waning immunity", arXiv:2609.04601 (2026), Section 1 (Assumptions 1.1-1.2, Proposition 1.1, Theorems 1.1-1.2, Proposition 1.2), Section 2 (Assumptions 2.1-2.3, Theorem 2.1, Corollary 2.1, Theorem 2.2) and Section 3 (Lemma 3.1, Theorems 3.1-3.2), <https://doi.org/10.48550/arXiv.2609.04601>.
