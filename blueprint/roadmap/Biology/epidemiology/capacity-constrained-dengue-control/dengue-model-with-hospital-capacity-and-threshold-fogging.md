# Dengue model with hospital capacity and threshold fogging

**Setting.** Humans are susceptible $S$, asymptomatically infected $A$, symptomatically infected $I$ or recovered $R$; mosquitoes are susceptible $U$ or infected $V$. Below the intervention thresholds the dynamics are
$$\begin{aligned}\dot S&=\Lambda_h-\beta_hSV-\mu_hS, & \dot A&=p\beta_hSV-(\alpha+\gamma_0+\mu_h)A,\\ \dot I&=(1-p)\beta_hSV+\alpha A-(\gamma_1+\mu_h+\delta)I, & \dot R&=\gamma_0A+\gamma_1I-\mu_hR,\\ \dot U&=\Lambda_m-\beta_{m1}UA-\mu_mU, & \dot V&=\beta_{m1}UA-\mu_mV,\end{aligned}$$
where a fraction $p$ of new human infections is asymptomatic, asymptomatic humans develop symptoms at rate $\alpha$ or recover at rate $\gamma_0$, symptomatic humans are treated and recover at rate $\gamma_1$ or die at rate $\delta$, and (in this regime) mosquitoes acquire infection from asymptomatic, untreated humans. The full model is **piecewise smooth**: when the number of symptomatic cases reaches a fraction $kC$ of the hospital capacity $C$ ($0<k<1$), threshold-triggered fogging adds a mosquito mortality term; when $I\ge C$ the hospital saturates and the treatment flux is capped at capacity.

**Theorem 1 (regime $I<kC$).** The model always has the dengue-free equilibrium $\mathcal E_0=(\Lambda_h/\mu_h,0,0,0,\Lambda_m/\mu_m,0)$, and has a unique endemic equilibrium if and only if $\mathcal R_0>1$, where
$$\mathcal R_0=\sqrt{\,p\,\frac{\Lambda_h\Lambda_m\beta_h\beta_{m1}}{\mu_h\,\mu_m^2\,(\alpha+\gamma_0+\mu_h)}\,}.$$

**Theorems 2-4 (local stability).** $\mathcal E_0$ is locally asymptotically stable if $\mathcal R_0<1$ and unstable if $\mathcal R_0>1$; the endemic equilibrium is locally asymptotically stable whenever it exists. In the fogging regime $kC\le I<C$ mosquito mortality becomes $\mu_m+\eta$ and the endemic equilibrium is locally asymptotically stable when $\mathcal R_{0\eta}=\mathcal R_0/(1+\eta/\mu_m)>1$.

## Expansion

The next-generation matrix couples the asymptomatic human class and the infected mosquito class: an infected mosquito produces $\beta_h(\Lambda_h/\mu_h)/\mu_m$ human infections, a fraction $p$ of them asymptomatic, and each asymptomatic human infects $\beta_{m1}(\Lambda_m/\mu_m)/(\alpha+\gamma_0+\mu_h)$ mosquitoes, so $\mathcal R_0$ is the geometric mean of the two transmission legs. Because the vector field switches on the surfaces $I=kC$ and $I=C$, the global dynamics are those of a Filippov system: equilibria of each smooth piece may be real or virtual, sliding motion can occur on the switching surfaces, and numerical continuation reveals pseudo-equilibria and oscillations created by the interplay of limited hospital capacity with intermittent fogging, which smooth models with unlimited capacity and continuous fogging cannot capture.

## Sources

- D. Aldila, J. Páez Chávez, A. Gökçe, T. Götz, "A mathematical model of dengue transmission incorporating hospital capacity and threshold-based fogging interventions", arXiv preprint (2026), Theorems 1-4, Section 4, <https://doi.org/10.48550/arXiv.2607.18140>.
