# Phase diagram of the two-hit waiting time in the spatial growth model

**Model.** Cells fill the $d$-dimensional torus $[0,L]^d$ of volume $N = L^d$; every point starts with type $0$. Mutations to type $1$ arrive as a space–time Poisson process of rate $\mu_1$ per unit volume; inside type-$1$ regions, mutations to type $2$ arrive at rate $\mu_2$ per unit volume. Each mutation spreads as a ball whose radius grows at speed $\alpha$, taking over points of lower type (a continuum limit of the biased voter model for clonal expansion in a tissue). Let $\sigma_2$ be the first time some point has type $2$, $\gamma_d$ the volume of the unit ball, and $\beta_2 = (N\mu_1\mu_2\alpha^d)^{-1/(d+2)}$. All parameters may depend on $N$, and limits are as $N \to \infty$. The fixation time of one mutant is of order $N^{1/d}/\alpha$, so the comparison of $\mu_1$ with $\alpha/N^{(d+1)/d}$ decides whether mutants sweep before the next one appears.

**Theorem.** Let $W \sim \mathrm{Exp}(1)$.

*(1)* *(Fast sweep, rare second hit.)* If $\mu_1 \ll \alpha/N^{(d+1)/d}$ and $\mu_2 \ll \mu_1$, then $N\mu_2\sigma_2 \Rightarrow W$.

*(2)* *(Many small type-1 regions, deterministic coverage.)* If $\mu_1 \gg \alpha/N^{(d+1)/d}$ and $(\mu_1\alpha^d)^{1/(d+1)}/N \ll \mu_2 \ll (N\mu_1)^{d+1}/\alpha^d$, then

$$\mathbb{P}(\sigma_2 > \beta_2t) \to \exp\Big(-\frac{\gamma_dt^{d+2}}{(d+1)(d+2)}\Big).$$

*(3)* *(Overlapping coverage.)* If $\mu_1 \gg \alpha/N^{(d+1)/d}$ and $N\mu_2/(\mu_1\alpha^d)^{1/(d+1)} \to c \in (0,\infty)$, then

$$\mathbb{P}(\sigma_2 > \beta_2t) \to \exp\Big(-c^{(d+1)/(d+2)}\int_0^t\Big(1 - \exp\Big(-\frac{\gamma_du^{d+1}}{(d+1)c^{(d+1)/(d+2)}}\Big)\Big)du\Big).$$

*(4)* *(Space saturated before the second hit.)* If $\mu_1 \gg \alpha/N^{(d+1)/d}$ and $\mu_2 \ll (\mu_1\alpha^d)^{1/(d+1)}/N$, then $N\mu_2\sigma_2 \Rightarrow W$.

*(5)* *(Critical first rate, rare second hit.)* If $\mu_1 \asymp \alpha/N^{(d+1)/d}$ and $\mu_2 \ll (N\mu_1)^{d+1}/\alpha^d$, then $N\mu_2\sigma_2 \Rightarrow W$.

Together with the regimes where the first mutation is rate-limiting ($N\mu_1\sigma_2 \Rightarrow W$), the sum-of-exponentials regime $\mu_2/\mu_1 \to c$ under fast sweeps, the nucleation regime of comparable time scales, and the [critical regime](critical-scaling-limit-of-spatial-mutation-waiting-times.md), these cover all eleven parameter regimes for $\sigma_2$.

## Depends on

- [Critical scaling limit of spatial mutation waiting times](critical-scaling-limit-of-spatial-mutation-waiting-times.md)

## Expansion

At time $t$, a point is covered by type $1$ with probability $q(t) = 1 - \exp(-\gamma_d\mu_1\alpha^dt^{d+1}/(d+1))$, since type-$1$ mutations born at time $r$ cover a ball of volume $\gamma_d(\alpha(t-r))^d$. When many independent small regions exist, the covered volume concentrates at $Nq(t)$ and

$$\mathbb{P}(\sigma_2 > t) \approx \exp\Big(-\int_0^tN\mu_2q(r)\,dr\Big).$$

Linearizing $q$ gives part 2 (exponent $d+2$); keeping $q$ exactly when the second hit coincides with substantial coverage gives part 3; and once $q \approx 1$ the second hit arrives at the full rate $N\mu_2$, giving parts 1, 4 and 5. The rigorous proofs control the variance of the covered volume and the overlap of regions with concentration lemmas.

## Sources

- Jasmine Foo, Kevin Leder, Jason Schweinsberg, "Mutation timing in a spatial model of evolution", arXiv:2001.01175 (2020): Section 2 (Cases 1–11 and heuristics), Theorem 2 (Case 10), Theorem 10 parts 1–2 (Cases 6 and 7), Theorem 11 (Case 8), Theorem 1 (Cases 1–3). <https://doi.org/10.48550/arXiv.2001.01175>
