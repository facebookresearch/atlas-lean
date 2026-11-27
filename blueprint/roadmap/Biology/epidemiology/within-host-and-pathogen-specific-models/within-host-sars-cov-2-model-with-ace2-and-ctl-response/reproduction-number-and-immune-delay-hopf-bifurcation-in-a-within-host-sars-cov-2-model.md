# Reproduction number and immune-delay Hopf bifurcation in a within-host SARS-CoV-2 model

**Model.** Let $T, I, V, E, C$ be uninfected epithelial cells, infected cells, free virus, ACE2 receptor level and cytotoxic T lymphocytes. With latent delay $\tau_1$, immune-activation delay $\tau_2$, drug efficacies $\epsilon_1, \epsilon_2 \in [0,1)$ and nonlytic inhibition $1 + qC$,

$$\begin{aligned}
\dot T &= \lambda_1 - (1-\epsilon_1)\frac{\beta EVT}{1+qC} - d_T T,\\
\dot I &= (1-\epsilon_1)\frac{e^{-d_I\tau_1}\beta E(t-\tau_1)V(t-\tau_1)T(t-\tau_1)}{1 + qC(t-\tau_1)} - d_I I - pIC,\\
\dot V &= (1-\epsilon_2)m d_I I - d_V V, \qquad \dot E = \lambda_2 - \theta\beta EVT - d_E E,\\
\dot C &= \alpha I(t-\tau_2)C(t-\tau_2)\Big(1 - \frac{C(t-\tau_2)}{C_{\max}}\Big) - d_C C,
\end{aligned}$$

with positive parameters ($m$ is the burst size per infected-cell lifetime).

**Reproduction number.** For the delay-free system the next-generation method gives

$$R_0 = \frac{(1-\epsilon_1)(1-\epsilon_2)\,m\beta\lambda_1\lambda_2}{d_V d_E d_T}.$$

(The source's eq. (R0) of arXiv:2412.12315 is the drug-free value $m\beta\lambda_1\lambda_2/(d_Vd_Ed_T)$, the case $\epsilon_1 = \epsilon_2 = 0$; the drug factors are included here because the model above carries them.)

**Theorem (delay-free stability).**
1. The infection-free equilibrium $E_0 = (\lambda_1/d_T, 0, 0, \lambda_2/d_E, 0)$ is stable for $R_0 < 1$ and unstable for $R_0 > 1$.
2. The CTL-free equilibrium $E_1$ is asymptotically stable if and only if the coefficients $\alpha_1, \dots, \alpha_4$ of its quartic characteristic polynomial satisfy the Routh–Hurwitz conditions $\alpha_i > 0$, $\alpha_1\alpha_2 - \alpha_3 > 0$, $(\alpha_1\alpha_2 - \alpha_3)\alpha_3 - \alpha_1^2\alpha_4 > 0$.
3. The coexistence equilibrium $E^*$ is asymptotically stable if and only if the coefficients of its quintic characteristic polynomial satisfy the five-dimensional Routh–Hurwitz conditions.

**Theorem (immune delay, $\tau_1 = 0$).** Write the characteristic equation at $E^*$ as $P(\lambda) + Q(\lambda)e^{-\lambda\tau_2} = 0$ and let $H(l) = |P(i\sqrt l)|^2 - |Q(i\sqrt l)|^2$ be the associated quintic in $l = \omega^2$. If $H$ has no positive root, $E^*$ is locally asymptotically stable for every $\tau_2 \ge 0$. If $H$ has a positive root (explicit sign conditions on its coefficients), then there is a critical delay $\tau_2^*$ such that $E^*$ is locally asymptotically stable for $\tau_2 \in [0, \tau_2^*)$, and, under a transversality condition, $E^*$ undergoes a Hopf bifurcation as $\tau_2$ crosses $\tau_2^*$, producing sustained oscillations of virus and CTL levels.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

Infection requires both target cells and ACE2 receptors, so the bilinear-in-$E$ and $T$ incidence makes $R_0$ proportional to the product $\lambda_1\lambda_2/(d_Td_E)$ of their disease-free levels times the viral yield $m\beta/d_V$. With infected compartments $(I, V)$, new infections $F = \begin{pmatrix}0 & (1-\epsilon_1)\beta\lambda_1\lambda_2/(d_Td_E)\\ 0 & 0\end{pmatrix}$ and transitions $\mathcal V = \begin{pmatrix} d_I & 0\\ -(1-\epsilon_2)md_I & d_V\end{pmatrix}$ at $E_0$, the spectral radius of $F\mathcal V^{-1}$ is the stated $R_0$, and the drug efficacies enter as the factors $1-\epsilon_1$ and $1-\epsilon_2$. Purely imaginary roots $\lambda = i\omega$ of the delayed characteristic equation exist exactly when $|P(i\omega)| = |Q(i\omega)|$, i.e. at positive roots of $H$; the smallest delay at which such a root appears is $\tau_2^*$, and a nonzero crossing speed gives the Hopf bifurcation.

## Sources

- Amar N. Chatterjee, Teklebirhan Abraha, Fahad Al Basir and Delfim F. M. Torres, "A model for the dynamics of COVID-19 infection transmission in human with latent delay", *Afrika Matematika* 36 (2025), 15, <https://doi.org/10.1007/s13370-024-01226-0>. Preprint version: arXiv:2412.12315 (2024), model in Section 2, Theorems 2–4 (Section 3), Lemma 5 and Theorem 6 (Section 4), <https://doi.org/10.48550/arXiv.2412.12315>.
