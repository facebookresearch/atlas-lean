# Reproduction and invasion numbers for dengue-Zika co-circulation

**Setting.** Humans (constant total $N_h$, birth and death rate $\mu$) and mosquitoes (constant total $N_v$, rate $\mu_v$) carry two arboviruses: dengue (D) and Zika (Z). Mosquito-to-human transmission rates are $\beta_{hd}, \beta_{hz}$, human-to-mosquito rates $\beta_{vd}, \beta_{vz}$, human recovery rates $\gamma_d, \gamma_z$, and Zika is also sexually transmitted between humans at rate $\beta_s$. Coinfected mosquitoes transmit dengue and Zika with relative factors $\nu_d, \nu_z$, and prior Zika (dengue) immunity multiplies susceptibility to dengue (Zika) by $k_d$ ($k_z$), with $k > 1$ modeling antibody-dependent enhancement.

**Basic reproduction number.** The next-generation matrix at the disease-free state is block diagonal by virus, so $\mathcal R_0 = \max\{\rho_d, \rho_z\}$ with

$$\rho_d = \sqrt{\frac{N_v}{N_h}\,\frac{\beta_{vd}}{\mu_v}\,\frac{\beta_{hd}}{\mu + \gamma_d}}, \qquad \rho_z = \frac12\left[\frac{\beta_s}{\mu+\gamma_z} + \sqrt{\Big(\frac{\beta_s}{\mu+\gamma_z}\Big)^2 + 4\,\frac{N_v}{N_h}\,\frac{\beta_{vz}}{\mu_v}\,\frac{\beta_{hz}}{\mu+\gamma_z}}\right].$$

The disease-free equilibrium is locally asymptotically stable when $\mathcal R_0 < 1$. Here $\rho_d^2 = \mathcal R_d$ is the two-generation (human to mosquito to human) dengue number, and $\rho_z$ is the dominant root of $\rho^2 - \frac{\beta_s}{\mu+\gamma_z}\rho - \frac{N_v \beta_{vz}\beta_{hz}}{N_h \mu_v(\mu+\gamma_z)} = 0$, combining direct sexual transmission with the vector cycle.

**Invasion reproduction numbers.** Treating the resident virus as part of the environment and applying the next-generation construction at its endemic boundary equilibrium, the dengue invasion number into a Zika-endemic population factors as

$$\tilde{\mathcal R}_d = \mathcal R_d\, K_{vd}\, K_{hd},$$

where $K_{vd}$ is the average relative dengue infectivity of mosquitoes at the Zika-only equilibrium (weight $\nu_d$ for mosquitoes that are or will become Zika-infected before death, weight $1$ otherwise) and $K_{hd}$ is the average relative dengue susceptibility-infectivity of humans there (weight $k_d$ for those that have recovered from Zika before acquiring dengue, $1$ otherwise). When $k_d = \nu_d = 1$, $\tilde{\mathcal R}_d = \mathcal R_d$. The Zika-endemic equilibrium is locally asymptotically stable if $\rho_z > 1$ and $\tilde{\mathcal R}_d < 1$; symmetrically for the dengue-endemic equilibrium with $\tilde{\mathcal R}_z$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
## Expansion

For dengue the $2 \times 2$ block of $FV^{-1}$ is $\begin{pmatrix} 0 & b \\ c & 0 \end{pmatrix}$ with $b = \beta_{hd}/\mu_v$, $c = N_v\beta_{vd}/(N_h(\mu+\gamma_d))$, whose spectral radius is $\sqrt{bc}$; for Zika the human-to-human entry $\beta_s/(\mu+\gamma_z)$ fills the diagonal and the characteristic quadratic gives $\rho_z$. Since $\sqrt{bc} < 1$ iff $bc < 1$, the threshold can be stated with either $\rho_d$ or $\mathcal R_d$. At the Zika-only equilibrium the dengue-infected subsystem has new-infection rates weighted by the resident Zika state of each host, and every dengue-infected class is entered either directly or after a Zika transition; computing $FV^{-1}$ there sums these branches, and the branch probabilities (for example $\beta_{vz}I_z^\ast/(\beta_{vz}I_z^\ast + \mu_v N_h)$ that a mosquito acquires Zika before dying) produce the averages $K_{vd}$ and $K_{hd}$. Numerically, coexistence is stable when both invasion numbers exceed one.

## Sources

- O. Olawoyin, C. Kribs, "Coinfection, Altered Vector Infectivity, and Antibody-Dependent Enhancement: The Dengue-Zika Interplay", Bulletin of Mathematical Biology 82(1) (2020) 13, Sections "Basic Reproductive Number" and "IRNs", <https://doi.org/10.1007/s11538-019-00681-2>, PMCID PMC7223258.
