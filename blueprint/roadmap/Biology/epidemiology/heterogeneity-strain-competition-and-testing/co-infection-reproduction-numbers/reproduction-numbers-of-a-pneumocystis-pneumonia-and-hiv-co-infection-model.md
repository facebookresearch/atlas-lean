# Reproduction numbers of a Pneumocystis pneumonia and HIV co-infection model

**Model.** A population with recruitment $\Lambda$ and natural mortality $\mu$ is split into susceptibles $S$; Pneumocystis pneumonia (PCP) carriers $C$, PCP infected $I_P$ and PCP-recovered $R$; HIV-infected $I_H$, AIDS $I_A$ and HIV-treated $I_T$; co-infected $I_{HP}$, $I_{AP}$ and co-infection-treated $T$. The forces of infection are

$$\alpha_P=\frac{\rho c(\omega C+I_P+\theta_1I_{HP}+\theta_2I_{AP})}{N},\qquad \alpha_H=\frac{\eta k(I_H+a_1I_{HP}+a_2I_A+a_3I_{AP})}{N},$$

with contact rates $c,k$, transmission probabilities $\rho,\eta$, relative infectiousness $\omega$ of carriers and $a_1<a_2<a_3$, $\theta_1<\theta_2$ of the HIV and co-infected classes. A fraction $\xi$ of new PCP infections become carriers, who develop symptoms at rate $\beta$ or clear at rate $\pi$; PCP infecteds recover at rate $\epsilon$ or die at rate $\nu_P$; recovered individuals lose immunity at rate $\gamma$; HIV progresses to AIDS at rate $\lambda_1$, AIDS kills at rate $\nu_A$, and HIV and AIDS patients are treated at rates $\tau_1,\tau_2$. Set $k_1=\beta+\pi+\mu$, $k_2=\epsilon+\mu+\nu_P$, $q_1=\tau_1+\lambda_1+\mu$, $q_2=\tau_2+\nu_A+\mu$.

**Theorem (sub-model thresholds).** The HIV/AIDS sub-model ($C=I_P=R=I_{HP}=I_{AP}=T=0$) has

$$\mathcal R_{0H}=\frac{\eta k}{q_1q_2}\big(q_2+a_2\lambda_1\big);$$

its disease-free equilibrium is globally asymptotically stable (and the only equilibrium) when $\mathcal R_{0H}\le1$, and its endemic equilibrium is globally asymptotically stable when $\mathcal R_{0H}>1$ (Lyapunov functions with LaSalle's principle). The PCP sub-model has

$$\mathcal R_{0P}=\frac{\rho c}{k_1k_2}\Big(\xi(k_2\omega+\beta)+(1-\xi)k_1\Big),$$

with locally asymptotically stable disease-free equilibrium when $\mathcal R_{0P}<1$ (globally under the Castillo-Chavez conditions) and globally stable endemic equilibrium when $\mathcal R_{0P}>1$. For the full co-infection model the next-generation reproduction number is

$$\mathcal R_0=\max\{\mathcal R_{0P},\mathcal R_{0H}\},$$

and the disease-free equilibrium is locally asymptotically stable when $\mathcal R_0<1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

In the HIV sub-model an infected individual spends mean time $1/q_1$ in $I_H$, infecting at rate $\eta k$, and with probability $\lambda_1/q_1$ progresses to AIDS, where it spends mean time $1/q_2$ infecting at rate $\eta ka_2$; summing gives $\mathcal R_{0H}=\frac{\eta k}{q_1}+\frac{\lambda_1}{q_1}\frac{\eta ka_2}{q_2}$. In the PCP sub-model a new infection is a carrier with probability $\xi$, transmitting at rate $\rho c\omega$ for mean time $1/k_1$ and becoming symptomatic with probability $\beta/k_1$, after which it transmits at rate $\rho c$ for mean time $1/k_2$; otherwise it is symptomatic from the start. HIV treatment rates $\tau_1,\tau_2$ enter $q_1,q_2$ and lower $\mathcal R_{0H}$, while the co-infection classes do not change the threshold at the disease-free state because the two infections interact there only through higher-order terms; the model is used to quantify how PCP treatment of each contagious stage reduces the co-infection burden among people on antiretroviral therapy.

## Sources

- Michael Byamukama, Damian Kajunguri and Martin Karuhanga, "A Mathematical Model for the Co-infection Dynamics of Pneumocystis Pneumonia and HIV/AIDS with Treatment", Science Journal of Applied Mathematics and Statistics 12 (2024), 48–63, <https://doi.org/10.11648/j.sjams.20241204.11>; numbering as in arXiv:2306.04407: Section 2 (model equations and forces of infection) and Section 3 (Theorems 1–7 on the HIV/AIDS, PCP and full co-infection models, next-generation computation of $\mathcal R_0$).
