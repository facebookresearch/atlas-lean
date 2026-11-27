# EpiSLFV process and its reproduction number

**Model.** Fix a dimension $d\ge 1$, a recovery rate $\gamma>0$ and a $\sigma$-finite measure $\nu$ on $(0,\infty)\times(0,1]$ (radius $r$, impact $u$) with

$$\int_0^1\!\!\int_0^\infty u\,r^d\,\nu(dr,du)<\infty .$$

The state is a measure $M$ on $\mathbb R^d\times\{0,1\}$ whose spatial marginal is Lebesgue measure, represented by a density $\omega_M:\mathbb R^d\to[0,1]$ of healthy individuals. For a ball $\mathcal B(z,r)$ of volume $V_r$ let

$$\Theta_{z,r,u}(\omega)=\omega-\mathbf 1_{\mathcal B(z,r)}\,u\,\omega,$$

which turns a fraction $u$ of the healthy individuals in the ball into infected ones. For test functions $\Psi(M)=F(\langle f,\omega_M\rangle)$ with $F\in C^1(\mathbb R)$, $f\in C_c(\mathbb R^d)$, the generator is

$$\mathcal G\Psi(M)=\gamma\,\langle f,1-\omega_M\rangle F'(\langle f,\omega_M\rangle)+\int_{\mathbb R^d}\!\int_0^1\!\!\int_0^\infty\frac1{V_r}\int_{\mathcal B(z,r)}(1-\omega_M(z'))\,dz'\,\big(\Psi(\Theta_{z,r,u}\omega_M)-\Psi(\omega_M)\big)\,\nu(dr,du)\,dz .$$

The first term is recovery at rate $\gamma$; the second says an event over $\mathcal B(z,r)$ samples a uniform individual in the ball and, if it is infected, infects a fraction $u$ of the healthy individuals there.

**Well-posedness.** For every initial state $M^0$, the martingale problem $(\mathcal G,\delta_{M^0})$ is well-posed; its solution is the $(\gamma,\nu)$-EpiSLFV process.

**Reproduction number.** Define

$$\mathrm R_0(\gamma,\nu)=\frac1\gamma\int_0^1\!\!\int_0^\infty u\,V_r\,\nu(dr,du),$$

the expected infected volume produced per unit time by one infected individual divided by the recovery rate. The process goes extinct if $\mathbb E\langle \mathbf 1_A,1-\omega_{M_t}\rangle\to 0$ for every compact $A$ of positive volume.

**Subcritical extinction.** Assume in addition $\int_0^1\!\int_0^\infty r^d\,\nu(dr,du)<\infty$ and let $M^0$ be an epidemic initial condition (the infected density exceeds some $\varepsilon>0$ on a compact set of positive volume and vanishes outside it). If $\mathrm R_0(\gamma,\nu)<1$, then

$$\lim_{t\to\infty}\mathbb E\big[\langle\mathbf 1_{\mathbb R^d},1-\omega_{M_t}\rangle\big]=0,$$

so the total expected infected mass vanishes.

## Depends on

- [SIS epidemic model](../../sis-epidemic-model/README.md)

## Expansion

Duality: the $k$-point moments $\mathbb E\int\psi(x_1,\dots,x_k)\prod_j\omega_{M_t}(x_j)\,dx$ equal expectations over an ancestral process of infected lineages, a spatial branching process in which a lineage covered by an event branches into the lineages of the sampled parent while recoveries kill lineages at rate $\gamma$; this gives uniqueness, and existence follows from a quenched construction driven by a space-time Poisson point process of events. The expected infected mass $m_t$ satisfies $m_t'\le(\gamma\mathrm R_0-\gamma)\,m_t$ because each infected point lies in events at total rate $\int uV_r\,\nu$, which gives exponential decay when $\mathrm R_0<1$. The candidate $\mathrm R_0$ is conjectured to be a sharp threshold at $1$, as in non-spatial SIS.

## Sources

- A. Louvet, B. Wiederhold, "A new stochastic SIS-type modelling framework for analysing epidemic dynamics in continuous space", *Stochastic Processes and their Applications* 195 (2026), 104896, Section 2 (generator, Theorem 2.1, Definitions 2.3 and 2.12, Proposition 2.15), <https://doi.org/10.1016/j.spa.2026.104896> (preprint arXiv:2502.02106).
