# Poissonian interacting trajectories as the clonal-interference limit of the Moran model

**The PIT.** Fix $\lambda>0$ and a probability measure $\gamma$ on $(0,\infty)$. Let $T_1<T_2<\cdots$ be a Poisson process of rate $\lambda$ on $\mathbb{R}_+$, $A_i$ i.i.d. $\sim\gamma$, and $B_i$ independent Bernoulli with $\mathbb{P}(B_i=1)=A_i/(1+A_i)$ (the survival probability of a mutant with advantage $A_i$). The *Poissonian system of interacting trajectories* $\mathscr{H}=(H_i)_{i\ge0}$ consists of continuous piecewise linear paths in $[0,1]$:
- $H_0(0)=1$, $H_i(0)=0$ for $i\ge1$, all slopes initially $0$;
- at time $T_i$ the slope of $H_i$ jumps from $0$ to $A_i$ if $B_i=1$;
- a trajectory reaching $0$ from above stays at $0$ forever;
- *kinking rule:* when a trajectory reaches height $1$ from below with slope $v^*$, the slopes of all trajectories with positive height are reduced by $v^*$.

The resident $\rho(t)$ is the unique trajectory at height $1$ with slope $0$; type fitnesses are $M_0=0$, $M_i=M_{\rho(T_i)}+A_i$, and the resident fitness is $F(t)=M_{\rho(t)}$.

**Moran prelimit.** In a Moran model of size $N$, new types arise at the jump times of a Poisson process of rate $\lambda/\log N$, in a randomly chosen individual of type $i$, with fitness $M^N_j=M^N_i+A_j$, $A_j\sim\gamma$ i.i.d.; reproduction is neutral plus a selective component at rate proportional to fitness differences. Let $X^N_i(t)$ be the size of type $i$ and $H^N_i(t)=\log(1+X^N_i(t\log N))/\log N$.

**Statements.**
1. *(Scaling limit.)* As $N\to\infty$, $H^N\to\mathscr{H}$ in distribution in $\mathcal{D}(\mathbb{R}_+,[0,1])^{\mathbb{N}_0}$, the fitness vectors $(M^N_1,\dots,M^N_i)$ converge to $(M_1,\dots,M_i)$, the mean population fitness $\bar F^N$ converges to $F$ in the Skorokhod $M_2$ topology, and the genealogical tree of types restricted to $\{0,\dots,i\}$ converges.
2. *(Speed of adaptation.)* If $\int a\,\gamma(da)<\infty$, then $F(t)/t\to\bar v\in(0,\infty)$ almost surely; if $\int a\,\gamma(da)=\infty$, then $F(t)/t\to\infty$ almost surely.
3. *(Fluctuations.)* If $\int a^2\gamma(da)<\infty$, there is $\sigma>0$ with $\big(\tfrac{F(nt)-\bar vnt}{\sigma\sqrt n}\big)_{t\ge0}\to W$, a standard Brownian motion, in $J_1$.

## Expansion

A surviving mutant with advantage $a$ over the resident grows like a supercritical branching process, so its log-size grows linearly at rate $a$ on the $\log N$ time-scale, while extinct mutants never leave height $0$; this gives the thinning $a/(1+a)$ and the linear pieces. When a clone becomes macroscopic, the mean fitness jumps by its relative advantage, so every other clone's relative growth rate drops by that amount, which is the kinking rule; clones overtaken by the new resident decline linearly and die at height $0$. The speed of adaptation is obtained by finding regeneration times, at which the system restarts in a state independent of the past, and expressing $F$ as a renewal-reward process; a finite first moment of $\gamma$ makes regeneration intervals and fitness gains integrable (law of large numbers), and a finite second moment gives the renewal-reward functional CLT.

## Sources

- Felix Hermann, Adrián González Casanova, Renato Soares dos Santos, András Tóbiás and Anton Wakolbinger, "From clonal interference to Poissonian interacting trajectories", Ann. Appl. Probab. 35 (2025), 2823–2865, <https://doi.org/10.1214/25-AAP2188>. Numbering follows the arXiv version, arXiv:2407.00793 (2024): Definition 2.4 (PIT dynamics), the definitions of resident type and fitness (Section 2.1), Theorem 2.7 (scaling limit), Theorem 2.8 (speed of adaptation) and Theorem 2.12 (functional central limit theorem), <https://doi.org/10.48550/arXiv.2407.00793>.
