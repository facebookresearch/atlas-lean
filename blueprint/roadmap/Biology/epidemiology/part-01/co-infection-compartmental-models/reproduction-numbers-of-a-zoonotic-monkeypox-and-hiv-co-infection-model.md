# Reproduction numbers of a zoonotic monkeypox and HIV co-infection model

**Model.** An animal reservoir $(S_n, I_n, R_n)$ with recruitment $\Lambda_n$ transmits monkeypox within itself with force $\lambda_n = \beta_{n1} c_{n1} I_n / N_n$ and to humans. Humans are split into susceptibles $S$, monkeypox-only infected $I_m$ and recovered $R_m$, HIV-only $I_h$ and AIDS $A_h$, dually infected $I_{hm}$ and $A_{hm}$, and monkeypox-recovered HIV-positive $R_{hm}$ and $R_{am}$, with recruitment $\Lambda_h$ and natural mortality $\mu_h$. The forces of infection are

$$\lambda_m = \frac{\beta_{nm} c_n I_n}{N_n} + \frac{\beta_m c_m (I_m + \theta_1 I_{hm} + \theta_2 A_{hm})}{N_h}, \qquad
\lambda_h = \frac{\beta_h c_h \bigl(I_h + R_{hm} + \phi_1 I_{hm} + \phi_2 [A_h + R_{am} + \phi_3 A_{hm}]\bigr)}{N_h},$$

where $\theta_i, \phi_i > 1$ are infectiousness enhancements; HIV-positive individuals acquire monkeypox at the enhanced rates $\sigma_1 \lambda_m$ ($I_h$) and $\sigma_2 \lambda_m$ ($A_h$). Monkeypox infections end at rates $\rho_{m1}$ (recovery) and $d_m$ (death); HIV progresses to AIDS at rate $\rho_{a1}$ and AIDS kills at rate $d_a$.

**Reproduction numbers.** At the infection-free equilibrium $(\Lambda_n/\mu_n, 0, 0, \Lambda_h/\mu_h, 0, \dots, 0)$,

$$\mathcal{R}_0^{n} = \frac{\beta_{n1} c_{n1}}{\mu_n + \rho_n + d_n}, \qquad
\mathcal{R}_0^{m} = \frac{\beta_m c_m}{\mu_h + \rho_{m1} + d_m}, \qquad
\mathcal{R}_0^{h} = \frac{\beta_h c_h\, (\mu_h + d_a + \phi_2 \rho_{a1})}{(\mu_h + \rho_{a1})(\mu_h + d_a)},$$

for monkeypox in the reservoir, monkeypox between humans, and HIV between humans. With $\mathcal{R}_0 = \max\{\mathcal{R}_0^{m}, \mathcal{R}_0^{h}\}$, the infection-free equilibrium is locally asymptotically stable if $\mathcal{R}_0 < 1$ and $\mathcal{R}_0^{n} < 1$, and unstable if either exceeds $1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)
- [Unstable mode of the infected subsystem exactly when $R_0 > 1$](../../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-iff-one-lt-r0.md)

## Proof depends on

- [Reproduction number of a co-infection model as the maximum of submodel numbers](reproduction-number-of-a-co-infection-model.md)

## Expansion

At the infection-free state all co-infected classes are empty, so the linearization decouples. The reservoir does not depend on humans, human monkeypox receives spillover from $I_n$ but does not feed back to the reservoir, and HIV and monkeypox interact only through products of their infected classes, which vanish to first order. Ordering infected states as reservoir, human monkeypox, human HIV, the next-generation matrix is block lower-triangular, so its spectral radius is $\max\{\mathcal{R}_0^n, \mathcal{R}_0^m, \mathcal{R}_0^h\}$; spillover raises human incidence but cannot by itself sustain human-to-human monkeypox when $\mathcal{R}_0^m < 1$. Each entry is a transmission rate times an expected infectious duration: $\mathcal{R}_0^h$ sums time in $I_h$, $1/(\mu_h + \rho_{a1})$, and $\phi_2$-weighted time in $A_h$, reached with probability $\rho_{a1}/(\mu_h + \rho_{a1})$ and lasting $1/(\mu_h + d_a)$. The enhancement parameters $\sigma_i, \theta_i, \phi_1, \phi_3$ for co-infection do not enter the thresholds; they shape the endemic co-infection equilibrium, whose stability the paper analyses by centre-manifold and Lyapunov methods.

## Sources

- C. P. Bhunu, S. Mushayabasa, J. M. Hyman, "Modelling HIV/AIDS and monkeypox co-infection", Applied Mathematics and Computation 218 (2012) 9504–9518, Section 2 (Equations (3)–(10), Theorem 1), <https://doi.org/10.1016/j.amc.2012.03.042> (PMC9629068).
