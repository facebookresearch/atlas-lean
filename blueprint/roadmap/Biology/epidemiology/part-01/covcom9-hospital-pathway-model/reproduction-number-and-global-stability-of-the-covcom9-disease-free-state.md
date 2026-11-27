# Reproduction number and global stability of the CoVCom9 disease-free state

**Model.** The CoVCom9 model has nine compartments: susceptible $S$; exposed $E$ (asymptomatic, infectious with relative weight $\alpha_1$); symptomatic infectious $I$; quarantined suspects $Q$; test-positive $P$; hospitalized $H$; critical care $C$; fatal/terminal $F$; and recovered $R$. Infection follows standard incidence,

$$f = \varphi\,\frac{\alpha_1E + I + \alpha_2Q + \alpha_3P + \beta_1H + \beta_2C + \beta_3F}{N}\,S,\qquad N = S+E+I+Q+P+H+C+F+R .$$

The infected subsystem, written with total exit rates $\pi_E = \epsilon_1+\epsilon_2+\mu+d_1$, $\pi_I = \gamma_1+\gamma_2+\mu+d_2$, $\pi_Q = \upsilon_1+\upsilon_2+\mu+d_3$, and similarly $\pi_P, \pi_H, \pi_C, \pi_F$, is

$$E' = f - \pi_E E,\quad I' = \epsilon_1E - \pi_I I,\quad Q' = \epsilon_2E - \pi_Q Q,\quad P' = \gamma_1I + \upsilon_1Q - \pi_P P,$$

$$H' = \rho_1P + \eta C + \delta_2F - \pi_H H,\quad C' = \rho_2P + \kappa_2H - \pi_C C,\quad F' = \rho_3P + \kappa_3H - \pi_F F .$$

The source's (2.3f) prints $\delta_2Q$ in the $H$ equation; $\delta_2F$ is the term its (2.3h), $V$ (3.11) and $J_V$ (3.14), from which $\mathcal R_0$ (3.15) is computed, use, so the page writes $\delta_2F$. Susceptibles are recruited at rate $\Lambda$ and also receive released quarantined individuals and recovered individuals who lose immunity.

**Reproduction number.** Let $\Theta = \frac{\epsilon_1\gamma_1}{\pi_E\pi_I} + \frac{\epsilon_2\upsilon_1}{\pi_E\pi_Q}$ be the probability that an exposed individual becomes test-positive, and $\Delta = \pi_H\pi_C\pi_F - \delta_2\kappa_3\pi_C - \eta\kappa_2\pi_F$. Then

$$\mathcal{R}_0 = \varphi\Big\{\frac{\alpha_1}{\pi_E} + \frac{\epsilon_1}{\pi_E\pi_I} + \frac{\alpha_2\epsilon_2}{\pi_E\pi_Q} + \frac{\Theta}{\pi_P}\Big(\alpha_3 + \beta_1\frac{\rho_1\pi_C\pi_F + \delta_2\rho_3\pi_C + \eta\rho_2\pi_F}{\Delta} + \beta_2\frac{\rho_2\pi_H\pi_F + \kappa_2\rho_1\pi_F + \delta_2(\kappa_2\rho_3 - \kappa_3\rho_2)}{\Delta} + \beta_3\frac{\rho_3\pi_H\pi_C + \kappa_3\rho_1\pi_C + \eta(\kappa_3\rho_2 - \kappa_2\rho_3)}{\Delta}\Big)\Big\}.$$

This is the sum $\mathcal{R}_{0E} + \mathcal{R}_{0I} + \mathcal{R}_{0Q} + \mathcal{R}_{0P} + \mathcal{R}_{0H} + \mathcal{R}_{0C} + \mathcal{R}_{0F}$ of secondary infections generated in each infectious state.

**Theorem.** Solutions with nonnegative data remain nonnegative, $\limsup N(t) \le \Lambda/\mu$, and the corresponding region $\Omega$ is positively invariant. The disease-free equilibrium is globally asymptotically stable in $\Omega$ if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$.

## Expansion

$\mathcal{R}_0$ is the dominant eigenvalue of $FV^{-1}$, where $F$ has a single nonzero row (new infections enter only $E$). It therefore equals that row applied to the expected residence times $V^{-1}$. The coupled block $(H, C, F)$, with returns $C\to H$ and $F\to H$, produces the common denominator $\Delta$. For global stability, let $w$ be the vector of infectiousness weights $(\alpha_1, 1, \alpha_2, \alpha_3, \beta_1, \beta_2, \beta_3)$, so that $f = \varphi\,(w\cdot x)\,S/N$ for the infected vector $x$, and take the linear function $L = \Phi^\top x$ with $\Phi^\top = \varphi\,w^\top V^{-1}$. Since $S/N \le 1$, $x' \le (\varphi\,e_1 w^\top - V)x$, so $L' \le \varphi(w^\top V^{-1}e_1\,\varphi - 1)\,w\cdot x = \varphi(\mathcal{R}_0 - 1)\,w\cdot x \le 0$ when $\mathcal{R}_0 < 1$. LaSalle's invariance principle then gives convergence to the disease-free state. Fitted to Ghana's March–August 2020 data, the paper estimates $\mathcal{R}_0 \approx 3.1$. The testing rate is among the six parameters to which $\mathcal{R}_0$ is most sensitive.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../Analysis/not-yet-classified/la-salle/lasalle-invariant.md)
- [Threshold theorem, instability half, spectral form](../../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-jacobian-of-one-lt-r0.md)
- [Lyapunov's indirect method, instability](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md)

## Sources

- E. Acheampong, E. Okyere, S. Iddi, J. H. K. Bonney, J. A. D. Wattis and R. L. Gomes, "Modelling COVID-19 Transmission Dynamics in Ghana", arXiv:2102.02984 (2021), Section 2 (model), Lemmas 1–2, the $\mathcal{R}_0$ derivation in Section 3, and Theorem 1, <https://doi.org/10.48550/arXiv.2102.02984>.
- Published version: E. Acheampong, E. Okyere, S. Iddi, J. H. K. Bonney, J. K. K. Asamoah, J. A. D. Wattis and R. L. Gomes, "Mathematical modelling of earlier stages of COVID-19 transmission dynamics in Ghana", Results in Physics 34 (2022), 105193, <https://doi.org/10.1016/j.rinp.2022.105193>.
