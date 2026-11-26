# SEIR model with droplet and fomite inoculum pools

**Model.** Let $S, E, I_A, I_S, R$ be the numbers of susceptible, exposed (latent), pre-/asymptomatically infectious, symptomatically infectious and removed individuals, and let $D$ and $F$ be the amounts of free-living inoculum in airborne droplets and on surfaces (fomites). With mean stage durations $\tau_E, \tau_A, \tau_S$, inoculum lifetimes $\tau_D, \tau_F$, shedding rates $\beta_A, \beta_S$ (inoculum per infectious individual per unit time), uptake-infection rates $\beta_D, \beta_F$ (per susceptible per unit inoculum per unit time) and facemask factors $m_A, m_S, m_D, m_F$ multiplying the corresponding rates,

$$
\begin{aligned}
\dot S &= -(\beta_F m_F F + \beta_D m_D D)\,S, &
\dot E &= (\beta_F m_F F + \beta_D m_D D)\,S - E/\tau_E,\\
\dot I_A &= E/\tau_E - I_A/\tau_A, &
\dot I_S &= I_A/\tau_A - I_S/\tau_S, \qquad \dot R = I_S/\tau_S,\\
\dot D &= \beta_A m_A I_A + \beta_S m_S I_S - D/\tau_D, &
\dot F &= D/\tau_D - F/\tau_F .
\end{aligned}
$$

Droplets that are not inhaled deposit and become fomites. A mask factor below $1$ means the mask reduces that rate; $m_F > 1$ allows a mask to increase fomite risk (for example through face touching). A lock-down that multiplies every transmission rate $\beta_A, \beta_S, \beta_D, \beta_F$ by the same factor $q$ multiplies both shedding and uptake, so it reduces effective spread by the factor $q^2$.

**Basic reproduction number.** In a fully susceptible population of size $N \gg 1$ (without masks), one introduced exposed individual sheds in total $D_{\mathrm{total}} = \beta_A \tau_A + \beta_S \tau_S$ units of droplet inoculum, all of which eventually passes through the fomite pool as well ($F_{\mathrm{total}} = D_{\mathrm{total}}$). Each unit of droplet inoculum survives on average $\tau_D$ and each unit of fomite inoculum $\tau_F$, so

$$R_0 = (\beta_D \tau_D + \beta_F \tau_F)\,(\beta_A \tau_A + \beta_S \tau_S)\,N .$$

If $\mu = \beta_D \tau_D / (\beta_D \tau_D + \beta_F \tau_F) \in (0,1)$ is the fraction of transmission via droplets, the uptake rates are determined by $R_0$, $\mu$ and the durations:

$$\beta_D = \frac{\mu\, R_0}{(\beta_A \tau_A + \beta_S \tau_S)\, N\, \tau_D}, \qquad \beta_F = \frac{(1 - \mu)\, R_0}{(\beta_A \tau_A + \beta_S \tau_S)\, N\, \tau_F}, \qquad \frac{\beta_D}{\beta_F} = \frac{\mu}{1 - \mu}\,\frac{\tau_F}{\tau_D}.$$

With masks worn by everyone, $R_0$ is multiplied by the factor obtained by replacing $\beta_A, \beta_S, \beta_D, \beta_F$ with $m_A\beta_A, m_S\beta_S, m_D\beta_D, m_F\beta_F$; with $m_A = m_S = m$ the shedding term scales by $m$ and the result is $m\,(\mu\, m_D + (1 - \mu)\, m_F)\,R_0$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

The infected-and-inoculum subsystem is linear near the disease-free state with $S \approx N$. The expected sojourn of the index case in $I_A$ and $I_S$ is $\tau_A$ and $\tau_S$, so the expected total droplet output is $\beta_A \tau_A + \beta_S \tau_S$. A unit of droplet inoculum causes on average $\beta_D N \tau_D$ new infections before it deposits, and the deposited unit then causes $\beta_F N \tau_F$ more before losing viability; summing gives $R_0$. The same number is the spectral radius of the next-generation operator obtained by treating $E, I_A, I_S, D, F$ as the infected compartments, since new infections enter only through $E$, which makes the next-generation matrix rank one with its single nonzero eigenvalue equal to the expected number of infections caused by one exposed individual. The $q^2$ lock-down effect is the product of a factor $q$ on shedding and a factor $q$ on uptake. In the source analysis the population was split into facemask wearers and non-wearers sharing the same inoculum pools; the single-population form above is the model as written in the paper's equations.

## Sources

- R. O. J. H. Stutt, R. Retkute, M. Bradley, C. A. Gilligan, J. Colvin, "A modelling framework to assess the likely effectiveness of facemasks in combination with 'lock-down' in managing the COVID-19 pandemic", Proceedings of the Royal Society A (2020), Section 2(b) ("Susceptible–infected–removed model with free-living inoculum": model equations and $R_0$ calculation) and Table 1, <https://doi.org/10.1098/rspa.2020.0376> (PMC7428039).
