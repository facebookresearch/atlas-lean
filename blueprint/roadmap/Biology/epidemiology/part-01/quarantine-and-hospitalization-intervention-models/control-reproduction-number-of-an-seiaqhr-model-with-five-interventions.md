# Control reproduction number of an SEIAQHR model with five interventions

**Model.** Compartments: susceptible $S$, quarantined susceptible $S_q$, exposed $E$, symptomatic infectious $I$, asymptomatic infectious $A$, quarantined infected $Q$, hospitalized $H$, recovered $R$. Constant controls $\phi_1,\dots,\phi_5\in[0,1]$ represent personal protection ($\phi_1$), contact tracing and testing of exposed individuals ($\phi_2$), treatment of timely diagnosed ($\phi_3$, acting on $A$) and delayed diagnosed ($\phi_4$, acting on $I$) infected individuals, and treatment of hospitalized individuals ($\phi_5$). Assume $\Lambda, \beta, \sigma, \mu > 0$, the other rates $\ge 0$, and $\theta_1, \theta_2 \ge 0$ with $\theta_1 + \theta_2 \le 1$. With force of infection $\lambda=\beta(1-\phi_1)(I+\eta A+\rho H)$ and $\theta_3=1-\theta_1-\theta_2$,

$$\begin{aligned}\dot S&=\Lambda-\lambda S-(\omega+\mu)S+\varepsilon S_q, & \dot S_q&=\omega S-(\varepsilon+\mu)S_q,\\ \dot E&=\lambda S-(\sigma+\mu+\phi_2)E, & \dot I&=\theta_1\sigma E-(\alpha_i+\gamma_i+d+\mu+\phi_4)I,\\ \dot A&=\theta_2\sigma E-(\gamma_a+\mu+\phi_3)A, & \dot Q&=(\theta_3\sigma+\phi_2)E-(\alpha_q+\gamma_q+\mu)Q,\\ \dot H&=(\alpha_i+\phi_4)I+\phi_3A+\alpha_qQ-(\gamma_h+d+\mu+\phi_5)H, & \dot R&=(\gamma_h+\phi_5)H+\gamma_qQ+\gamma_iI+\gamma_aA-\mu R.\end{aligned}$$

**Theorem 1.** With $g_1=\sigma+\mu+\phi_2$, $g_2=\alpha_i+\gamma_i+d+\mu+\phi_4$, $g_3=\gamma_a+\mu+\phi_3$, $g_4=\alpha_q+\gamma_q+\mu$, $g_5=\alpha_i+\phi_4$, $g_6=\gamma_h+d+\mu+\phi_5$ and disease-free susceptible level $S^*=\Lambda(\varepsilon+\mu)/(\mu(\varepsilon+\omega+\mu))$, the control reproduction number is

$$R_c=\frac{(1-\phi_1)\beta S^*}{g_1g_2g_3g_4g_6}\Bigl(g_3g_4g_6\theta_1\sigma+g_3g_4g_5\rho\theta_1\sigma+g_2g_4g_6\eta\theta_2\sigma+g_2g_4\rho\theta_2\sigma\phi_3+g_2g_3\rho\alpha_q(\theta_3\sigma+\phi_2)\Bigr).$$

The disease-free equilibrium is locally asymptotically stable if $R_c<1$ and unstable if $R_c>1$ (Lemma 3), and globally asymptotically stable in the feasible region if $R_c\le1$ (Theorem 3). Setting all $\phi_i=0$ gives the basic reproduction number $R_0$ (Eqs. 10–11), which splits into contributions from symptomatic, asymptomatic and hospitalized transmission.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)
- [Unstable mode of the infected subsystem exactly when $R_0 > 1$](../../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-iff-one-lt-r0.md)

## Expansion

Follow one exposed individual in a fully susceptible population. It leaves $E$ at rate $g_1$, entering $I$, $A$ or $Q$ with probabilities $\theta_1\sigma/g_1$, $\theta_2\sigma/g_1$ and $(\theta_3\sigma+\phi_2)/g_1$. In $I$ it infects at rate $(1-\phi_1)\beta S^*$ for mean time $1/g_2$ and then moves to $H$ with probability $g_5/g_2$; in $A$ it infects at relative rate $\eta$ for mean time $1/g_3$ and moves to $H$ with probability $\phi_3/g_3$; from $Q$ it reaches $H$ with probability $\alpha_q/g_4$; in $H$ it infects at relative rate $\rho$ for mean time $1/g_6$. Summing the expected secondary infections over these paths and clearing denominators gives the five terms above, which is the spectral radius of the rank-one next-generation matrix. The source prints $g_6$ as $\gamma_h+d\mu+\phi_5$; the outflow of $H$ in the model is $\gamma_h+d+\mu+\phi_5$.

## Sources

- A. Abidemi, Z. M. Zainuddin, N. A. B. Aziz, "Impact of control interventions on COVID-19 population dynamics in Malaysia: a mathematical study", The European Physical Journal Plus (2021). <https://doi.org/10.1140/epjp/s13360-021-01205-5>, PMCID PMC7894251. Definition 1 (Eqs. 5a–5h), Theorem 1 (Eqs. 7–8), Lemma 3, Remark 1 and Theorem 3.
