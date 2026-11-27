# Reproduction ratio with adult-only transmission

**Model (Eq. 2).** Children ($C$) and adults ($A$) are each split into susceptible, latent, active and recovered classes. Children mature at rate $g$, all individuals die naturally at rate $\mu$, and only active adults $I_A$ transmit:

$$\begin{aligned}\dot S_C&=\Lambda+\theta_CR_C-\beta_CS_CI_A-(\mu+g)S_C, & \dot S_A&=gS_C+\theta_AR_A-\beta_AS_AI_A-\mu S_A,\\ \dot E_C&=\beta_CS_CI_A-(\alpha_C+\mu+g)E_C, & \dot E_A&=\beta_AS_AI_A+gE_C-(\alpha_A+\mu)E_A,\\ \dot I_C&=\alpha_CE_C-(\gamma_C+\mu+g+d_C)I_C, & \dot I_A&=\alpha_AE_A+gI_C-(\gamma_A+\mu+d_A)I_A,\\ \dot R_C&=\gamma_CI_C-(\mu+g+\theta_C)R_C, & \dot R_A&=\gamma_AI_A+gR_C-(\mu+\theta_A)R_A,\end{aligned}$$

with non-negative constant parameters. The feasible region $\{0\le N\le\Lambda/\mu\}$ is positively invariant, and the disease-free equilibrium has $S_C=\Lambda/(g+\mu)$, $S_A=g\Lambda/(\mu(g+\mu))$.

**Reproduction ratio (Eq. 4).** With $\eta_1=g+\mu$, $\eta_2=\alpha_C+\mu+g$, $\eta_3=\alpha_A+\mu$, $\eta_4=\gamma_C+\mu+g+d_C$, $\eta_5=\gamma_A+\mu+d_A$,

$$R_0=\frac{g\Lambda\bigl[\alpha_A\beta_A\eta_2\eta_4+\beta_C\mu(\alpha_A\eta_4+\alpha_C\eta_3)\bigr]}{\mu\,\eta_1\eta_2\eta_3\eta_4\eta_5}.$$

The disease-free equilibrium is locally asymptotically stable if $R_0<1$ and unstable if $R_0>1$. For $R_0>1$ there is an endemic equilibrium whose $I_A$ component is the unique positive root of a quadratic $\mathcal{A}x^2+\mathcal{B}x+\mathcal{C}$ with $\mathcal{A}>0$ and $\mathcal{C}=-(R_0-1)\mu\eta_1\cdots\eta_7<0$, where $\eta_6=\mu+g+\theta_C$ and $\eta_7=\mu+\theta_A$.

For a single unstructured population (Eq. 1) the corresponding ratio is $R_0^s=\alpha\beta\Lambda/(\mu(\alpha+\mu)(\gamma+\mu+d))$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Because only $I_A$ transmits, the next-generation matrix is $1\times1$: $R_0$ is the expected number of new active-adult-producing infections from one active adult. An active adult infects for mean time $1/\eta_5$, at rates $\beta_AS_A$ into $E_A$ and $\beta_CS_C$ into $E_C$. An $E_A$ individual reaches $I_A$ with probability $\alpha_A/\eta_3$. An $E_C$ individual reaches $I_A$ either by activating as a child and then maturing, with probability $(\alpha_C/\eta_2)(g/\eta_4)$, or by maturing while latent and then activating, with probability $(g/\eta_2)(\alpha_A/\eta_3)$. Hence

$$R_0=\frac{1}{\eta_5}\Bigl[\beta_A\frac{g\Lambda}{\mu\eta_1}\frac{\alpha_A}{\eta_3}+\beta_C\frac{\Lambda}{\eta_1}\Bigl(\frac{\alpha_Cg}{\eta_2\eta_4}+\frac{g\alpha_A}{\eta_2\eta_3}\Bigr)\Bigr],$$

which simplifies to Eq. 4. Since $\mathcal{A}>0>\mathcal{C}$ when $R_0>1$, the quadratic has exactly one positive root.

## Sources

- Fatmawati, U. Dyah Purwati, F. Riyudha, H. Tasman, "Optimal control of a discrete age-structured model for tuberculosis transmission", Heliyon (2020) e03030. <https://doi.org/10.1016/j.heliyon.2019.e03030>, PMCID PMC6940635. Sections 2–3, Eqs. (1)–(4).
