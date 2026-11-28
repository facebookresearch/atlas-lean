# Threshold dynamics and synchronisation of pulse vaccination in connected regions

**Model.** $N$ connected regions (patches) each have susceptible $S_i$, infectious $I_i$, recovered $R_i$ and an environmental pathogen reservoir $G_i$. With constant births $b_i$ (a fraction $p_i$ vaccinated at birth), deaths $\mu_i$, recovery $\gamma_i$, $\tau$-periodic direct and environmental transmission rates $\beta_{ij}(t)$, $\epsilon_{ij}(t)$, shedding $\xi_i(t)$ and decay $\nu_i(t)$ of the reservoir, and movement matrices $(m_{ij}),(k_{ij}),(l_{ij})$ for the three classes:

$$\dot S_i=(1-p_i)b_i-\mu_iS_i-S_i\sum_j\beta_{ij}(t)I_j-S_i\sum_j\epsilon_{ij}(t)G_j+\sum_jm_{ij}S_j,$$

$$\dot I_i=S_i\sum_j\beta_{ij}(t)I_j+S_i\sum_j\epsilon_{ij}(t)G_j-(\mu_i+\gamma_i)I_i+\sum_jk_{ij}I_j,\qquad \dot G_i=\xi_i(t)I_i-\nu_i(t)G_i,$$

with $R_i$ closing the system. In region $i$ a pulse vaccination at times $t_{i,n}$ (each region with its own $\tau$-periodic schedule) moves the fraction $\psi_{i,n}$ of susceptibles to $R_i$: $S_i(t_{i,n}^+)=(1-\psi_{i,n})S_i(t_{i,n}^-)$.

**Theorem (threshold).** Solutions exist, are unique and non-negative, and are ultimately uniformly bounded. The disease-free subsystem has a unique globally asymptotically stable $\tau$-periodic solution $\overline S(t)$. Let $R_e$ be the spectral radius of the next-generation operator of the infected subsystem linearized along $\overline S(t)$. If $R_e<1$ the disease-free periodic orbit is globally attracting; if $R_e>1$ (and the transmission/movement network is irreducible) the disease is uniformly persistent: there is $\delta>0$ with $\liminf_{t\to\infty}I_i(t)>\delta$ for all $i$ whenever infection is initially present. In the autonomous case, environmental transmission can be absorbed into direct transmission: $R_e$ equals that of the SIR network with $\tilde\beta_{ij}=\beta_{ij}+\frac{\xi_j}{\nu_j}\epsilon_{ij}$.

**Theorem (pulse synchronisation).** Take two patches with pulse vaccinations offset by a phase $\phi$, and no cross-infection or movement of infecteds. Then

$$R_e(\phi)=\max_{i=1,2}\frac1{(\mu_i+\gamma_i)\tau}\int_0^\tau\beta_i(t)\,\overline S_i^{\phi}(t)\,dt,$$

a $\tau$-periodic function of $\phi$. For identical patches with constant transmission ($b,\mu,\beta,\gamma$, susceptible migration rate $m$ and pulse fraction $\psi$ common), $R_e(\phi)$ is continuous, smooth off $\tau\mathbb Z$, has a strict local minimum at $\phi=0$ (synchronised pulses) and a critical point at $\phi=\tau/2$, with one-sided slopes

$$R_e'(0^+)=\widehat R_0\,\frac{m\,\psi^2\,(e^{\mu\tau}-1)^2}{2\tau\bigl(e^{\mu\tau}-(1-\psi)\bigr)^2}>0,\qquad R_e'(0^-)=-R_e'(0^+),$$

where $\widehat R_0=\beta b/(\mu(\mu+\gamma))$ is the reproduction number without pulse vaccination. Synchronising campaigns across connected regions therefore lowers the reproduction number locally, and with seasonal transmission the pulse timing relative to the transmission peak also matters.

## Depends on

- [Threshold dynamics of compartmental epidemic models in periodic environments](../../next-generation-matrix-and-the-basic-reproductio/threshold-dynamics-in-periodic-environments.md)

## Expansion

The disease-free system is a linear impulsive periodic system for $S$ that is cooperative through migration; its period map is a contraction, giving the unique attracting periodic solution. $R_e$ is defined, following Wang and Zhao, as the spectral radius of the next-generation operator on $\tau$-periodic functions, and its comparison with $1$ is equivalent to the sign of the Floquet exponent of the linearized infected system. Global attractivity for $R_e<1$ follows by comparison with this linear system, and persistence for $R_e>1$ from uniform persistence theory for the Poincaré map. In the two-patch case without infected movement, the infected subsystem is diagonal, so $R_e$ is the larger of the patch-wise time-averaged reproduction numbers along $\overline S_i^\phi$; migration of susceptibles mixes the two pulse responses, and differentiating the explicit periodic solution in $\phi$ gives the slopes. Out-of-phase pulses leave one patch replenished by migrants from the other while it is protected, which is why synchrony is locally optimal.

## Sources

- Cameron Browne, Robert Smith?, Lydia Bourouiba, "From regional pulse vaccination to global disease eradication: insights from a mathematical model of Poliomyelitis", arXiv (2013). Section 2 (model and Theorem 1), Section 3 (Proposition 2), Section 4 (reproduction number), Section 5 (Theorems 3 and 4), Section 6 (Theorem 5 pulse synchronisation, Theorem 6 environmental transmission). <https://doi.org/10.48550/arXiv.1309.0265>. Published version: Journal of Mathematical Biology 71(1) (2015), 215–253, <https://doi.org/10.1007/s00285-014-0810-y>; locators above refer to the arXiv version.
