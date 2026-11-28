# Marcus–Hush–Chidsey rate at a metal electrode

The Marcus–Hush–Chidsey model gives the oxidation and reduction rates at a metal electrode as Marcus rates for electrons of energy $x$ weighted by the Fermi–Dirac distribution and integrated over $x$.

For a one-electron redox reaction $\mathrm R\rightleftharpoons\mathrm O+e^-$ at a metal electrode, with
reorganization energy $\lambda>0$, thermal energy $k_BT>0$, overpotential $\eta$ and a prefactor $A>0$ (electronic
coupling and electrode density of states, taken uniform), the **Marcus–Hush–Chidsey (MHC) rates** are

$$k_{\mathrm{ox}}(\eta)=A\int_{-\infty}^{\infty}\exp\!\Big(-\frac{(x-\lambda+e\eta)^2}{4\lambda k_BT}\Big)\frac{dx}{1+e^{x/k_BT}},\qquad
k_{\mathrm{red}}(\eta)=A\int_{-\infty}^{\infty}\exp\!\Big(-\frac{(x-\lambda-e\eta)^2}{4\lambda k_BT}\Big)\frac{dx}{1+e^{x/k_BT}},$$

where $x$ is the electron energy relative to the Fermi level and $1/(1+e^{x/k_BT})$ is the Fermi–Dirac
occupation factor. Both integrals are absolutely convergent for every real $\eta$ (the integrand is bounded by a
Gaussian). The net reduction current is proportional to $k_{\mathrm{red}}-k_{\mathrm{ox}}$.

## Context

Research-level electrode kinetics. The model reproduced Chidsey's curved Tafel plots for redox-active self-assembled monolayers and is used for electron transfer at carbon–LiFePO$_4$ interfaces in porous battery electrodes.

## Depends on

None.

## Proof depends on

None.

## Expansion

A model definition (Zeng–Smith–Bai–Bazant Eq. (4)): the first factor is the classical Marcus rate for an electron of energy $x$ relative to the Fermi level, and the second is the Fermi–Dirac factor; with the signs of Eq. (4) the same factor serves both directions, and Eqs. (5)–(6) give the dimensionless form used in the asymptotic analysis.

## Sources

- Y. Zeng, R. Smith, P. Bai and M. Z. Bazant, Simple formula for Marcus–Hush–Chidsey kinetics, *Journal of Electroanalytical Chemistry* 735 (2014), 77–83; numbers from arXiv:1407.5370v1, Sec. II, Eqs. (3)–(4), and Eqs. (5)–(6) for the dimensionless form. [arXiv:1407.5370v1](https://arxiv.org/abs/1407.5370v1); [doi:10.1016/j.jelechem.2014.09.038](https://doi.org/10.1016/j.jelechem.2014.09.038)
