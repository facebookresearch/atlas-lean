# Initial-phase regimes of an SEIRS epidemic in a growing population

**Setting.** Use the SEIRS epidemic in a supercritical linear birth–death population (birth rate $\lambda$, natural death rate $\mu<\lambda$), with Malthusian parameter $\alpha$, basic reproduction number $R_0$ and minor-outbreak probability $\pi$ from [Threshold quantities of the SEIRS epidemic in a birth–death population](threshold-quantities-of-the-seirs-epidemic-in-a-birth-death-population.md). Start from $(S_n,E_n,I_n,R_n)(0)=(n-1,1,0,0)$, let $L_n=E_n+I_n$, $N_n=S_n+E_n+I_n+R_n$, and let $\pi_n=\mathbb{P}(L_n(t)<\sqrt n\ \forall t\ge0)$ be the probability of a minor outbreak.

**Theorem.** As $n\to\infty$:

1. If $\alpha\le0$, then for every $n$, $L_n(t)\to0$ almost surely: the disease dies out after infecting few.
2. If $0<\alpha<\lambda-\mu$, then $\pi_n\to\pi=\frac{\mu}{\mu+\nu}+\frac{\nu}{(\mu+\nu)R_0}$; with the remaining probability the *number* infected grows exponentially, $L_n(t)\sim e^{\alpha t}$, but the infected *fraction* $L_n(t)/N_n(t)\to0$, because the population outgrows the epidemic.
3. If $\alpha>\lambda-\mu$, then again $\pi_n\to\pi$, and with probability $1-\pi$ the number infected initially grows at rate $\alpha$, faster than the population.

In case 3, the deterministic large-population limit decides the long run: either disease deaths reduce the population growth rate but it stays supercritical and the infected fraction tends to an endemic equilibrium, or the disease deaths turn exponential population growth into exponential decay. In the deterministic SEIRS model of the source's Section 4, the population size is exactly constant and positive, $N(t)=N(0)>0$ for all $t>0$, if and only if the parameters satisfy

$$(\rho+\mu)\nu\kappa\sigma\lambda+\rho\kappa\nu\delta(\lambda-\mu)-(\rho+\mu)(\nu+\mu)(\delta+\mu+\sigma)\big[\kappa(\lambda-\mu)+\mu\sigma\big]=0$$

and the initial state is

$$S(0)=\frac{(\nu+\mu)(\delta+\mu+\sigma)}{\nu\kappa}N(0),\quad E(0)=\frac{(\delta+\mu+\sigma)(\lambda-\mu)}{\nu\sigma}N(0),\quad I(0)=\frac{\lambda-\mu}{\sigma}N(0),\quad R(0)=\frac{\delta(\lambda-\mu)}{\sigma(\rho+\mu)}N(0).$$

If $\lambda\ge\mu+\sigma$ the population stays supercritical regardless of the epidemic.

## Expansion

The comparison is between two exponential rates: $\alpha$ for infecteds and $\lambda-\mu$ for the disease-free population. If $\alpha<\lambda-\mu$ the susceptible pool, refreshed by births, grows faster than the infected count, so the branching approximation remains valid forever and prevalence vanishes. If $\alpha>\lambda-\mu$, infecteds reach a positive fraction in time of order $\log n$, after which the proportions follow the deterministic SEIRS system with births, and the excess mortality $\sigma I$ feeds back on $N$. Setting the growth rate of $N$ to zero at the endemic proportions gives the displayed balance condition.

## Depends on

- [Threshold quantities of the SEIRS epidemic in a birth–death population](threshold-quantities-of-the-seirs-epidemic-in-a-birth-death-population.md)

## Sources

- Tom Britton, Désiré Ouédraogo, "SEIRS epidemics in growing populations", arXiv:1703.09581 (2017): Section 3 (remark on $\lambda\ge\mu+\sigma$; main theorem for the initial phase and the following remark), Section 4 (deterministic SEIRS model and Theorem 4.2 characterizing constant population size, with (4.2) and (4.3)). <https://doi.org/10.48550/arXiv.1703.09581> Published version: Mathematical Biosciences (2018), as *SEIRS epidemics with disease fatalities in growing populations*, <https://doi.org/10.1016/j.mbs.2017.11.006>.
