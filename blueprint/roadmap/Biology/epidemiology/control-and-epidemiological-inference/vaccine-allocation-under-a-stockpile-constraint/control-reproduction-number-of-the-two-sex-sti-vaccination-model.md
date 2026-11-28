# Control reproduction number of the two-sex STI vaccination model

**Model.** In a heterosexual population of constant size, females ($k = f$) and males ($k = m$) are split into unvaccinated susceptible $S_k$, vaccinated susceptible $V_k$ and infectious $I_k$, with $N_k^* = S_k + V_k + I_k$ fixed. With recruitment equal to exit rate $d_k$, vaccination rate $u_k \ge 0$, vaccine effectiveness $\epsilon_k \in [0, 1]$ (vaccinated individuals have susceptibility $1 - \epsilon_k$), waning rate $\theta_k \ge 0$, recovery rate $\alpha_k$ without immunity, and sex-specific forces of infection

$$\lambda_{m\to f} = \frac{\beta_{m\to f} I_m}{N_m^*}, \qquad \lambda_{f\to m} = \frac{\beta_{f\to m} I_f}{N_f^*},$$

the dynamics are, for $(k, j) \in \{(f, m), (m, f)\}$,

$$\dot S_k = d_k N_k^* - (\lambda_{j\to k} + u_k + d_k) S_k + \alpha_k I_k + \theta_k V_k, \qquad \dot V_k = u_k S_k - (1-\epsilon_k)\lambda_{j\to k} V_k - (d_k + \theta_k) V_k,$$

$$\dot I_k = \lambda_{j\to k}\bigl(S_k + (1 - \epsilon_k) V_k\bigr) - (\alpha_k + d_k) I_k .$$

**Theorem.** The disease-free equilibrium has susceptible and vaccinated fractions

$$s_k^0 = \frac{d_k + \theta_k}{u_k + d_k + \theta_k}, \qquad v_k^0 = \frac{u_k}{u_k + d_k + \theta_k},$$

and the control reproduction number is

$$\mathcal R_c(u_f, u_m) = \sqrt{\frac{\beta_{f\to m}\bigl(s_m^0 + (1-\epsilon_m) v_m^0\bigr)}{\alpha_f + d_f} \cdot \frac{\beta_{m\to f}\bigl(s_f^0 + (1-\epsilon_f) v_f^0\bigr)}{\alpha_m + d_m}} .$$

The disease-free equilibrium is locally asymptotically stable if $\mathcal R_c < 1$ and unstable if $\mathcal R_c > 1$. Without vaccination,

$$\mathcal R_0 = \mathcal R_c(0, 0) = \sqrt{\frac{\beta_{f\to m}}{\alpha_f + d_f} \cdot \frac{\beta_{m\to f}}{\alpha_m + d_m}},$$

and $\mathcal R_c(u_f, u_m) < \mathcal R_0$ whenever $u_f, u_m > 0$ and $\epsilon_f, \epsilon_m > 0$.

Since each factor under the square root depends on only one sex's vaccination, vaccinating one sex alone multiplies $\mathcal R_0^2$ by that sex's effective susceptible fraction $s_k^0 + (1-\epsilon_k)v_k^0 = 1 - \epsilon_k v_k^0$; one-sex coverage $v_k^0 > (1 - \mathcal R_0^{-2})/\epsilon_k$ is therefore enough to push $\mathcal R_c$ below $1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Only the two infectious classes are infected compartments. New infections of females come only from infectious males and vice versa, so the next-generation matrix is anti-diagonal,

$$K = \begin{pmatrix} 0 & \dfrac{\beta_{m\to f}\bigl(s_f^0 + (1-\epsilon_f)v_f^0\bigr)}{\alpha_m + d_m}\dfrac{N_f^*}{N_m^*} \\[2mm] \dfrac{\beta_{f\to m}\bigl(s_m^0 + (1-\epsilon_m)v_m^0\bigr)}{\alpha_f + d_f}\dfrac{N_m^*}{N_f^*} & 0 \end{pmatrix},$$

whose spectral radius is the geometric mean of the two off-diagonal entries; the population-size ratios cancel in their product. The square root records that it takes two generations (female to male to female) for an infection to return to the same sex. The local stability statement is the van den Driessche–Watmough threshold theorem. The one-sex coverage bound follows by setting the other sex's factor to its unvaccinated value and solving $\mathcal R_0^2(1 - \epsilon_k v_k^0) < 1$. Which sex to prioritize under a limited stockpile is not decided by $\mathcal R_c$ alone; it depends on asymmetric transmissibility and on sex-specific disease burden in the objective.

## Sources

- F. Saldaña, V. Steindorf, A. K. Srivastav, N. Stollenwerk, M. Aguiar, "Optimal vaccine allocation for the control of sexually transmitted infections", *Journal of Mathematical Biology* 86 (2023), model (1)–(2), Eqs. (3)–(6) and Theorem 1. <https://doi.org/10.1007/s00285-023-01910-y> (PMC10103681).
