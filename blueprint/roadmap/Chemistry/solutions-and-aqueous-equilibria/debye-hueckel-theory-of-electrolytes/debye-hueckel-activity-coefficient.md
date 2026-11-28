# Debye–Hückel activity coefficient model

The Debye–Hückel model gives the single-ion activity coefficient of an ion of charge number $z_i$ as $\ln\gamma_i=-A_{\mathrm{DH}}z_i^2\sqrt{I_m}/(1+B_{\mathrm{DH}}a\sqrt{I_m})$, with constants fixed by the solvent and temperature.

For an ion of charge number $z_i$ in a solution of ionic strength $I_m\ge0$ ([molality basis](ionic-strength.md))
in a solvent of density $\rho_A^*>0$ and relative permittivity $\varepsilon_r>0$ at temperature $T>0$, the
**Debye–Hückel equation** models the molality-basis [activity coefficient](../../chemical-thermodynamics/reaction-gibbs-energy-and-equilibrium-constants/chemical-potential-in-terms-of-relative-activity.md) as

$$\ln\gamma_i=-\frac{A_{\mathrm{DH}}z_i^2\sqrt{I_m}}{1+B_{\mathrm{DH}}a\sqrt{I_m}},$$

$$A_{\mathrm{DH}}=\Big(\frac{N_A^2e^3}{8\pi}\Big)\big(2\rho_A^*\big)^{1/2}\big(\varepsilon_r\varepsilon_0RT\big)^{-3/2},\qquad
B_{\mathrm{DH}}=N_Ae\big(2\rho_A^*\big)^{1/2}\big(\varepsilon_r\varepsilon_0RT\big)^{-1/2},$$

where $a>0$ is the mean distance of closest approach of other ions. It comes from the
[screened potential](debye-hueckel-screened-potential.md): the atmosphere potential at the ion,
$\phi_{\mathrm{atm}}(a)=-(z_ie/4\pi\varepsilon_r\varepsilon_0)\kappa/(1+\kappa a)$, is assumed to scale linearly with the central
charge at fixed bulk parameters, so that charging the ion from $0$ to $z_ie$ costs the work
$w'=-(z_i^2e^2/8\pi\varepsilon_r\varepsilon_0)\kappa/(1+\kappa a)$, identified with $RT\ln\gamma_i/N_A$; the concentration basis
is then converted with the dilute-solution approximation $c_i\approx\rho_A^*m_i$, $I_c\approx\rho_A^*I_m$. The model
considers only electrostatic ion–ion interactions and the linearized Boltzmann law and is accurate only in dilute
solution.

## Context

Graduate physical chemistry. In electrochemical energy storage the Debye–Hückel activity coefficients correct the Nernst equation of dilute electrolytes; concentrated battery electrolytes need further terms.

## Depends on

- [Ionic strength](ionic-strength.md)
- [Chemical potential in terms of relative activity](../../chemical-thermodynamics/reaction-gibbs-energy-and-equilibrium-constants/chemical-potential-in-terms-of-relative-activity.md)
- [Debye–Hückel screened potential around an ion](debye-hueckel-screened-potential.md)

## Proof depends on

None.

## Expansion

A model definition. DeVoe's Eq. 10.5.4 integrates the atmosphere potential produced by charge $\alpha z_ie$, proportional to $\alpha$, against $d(\alpha z_ie)$ for $\alpha\in[0,1]$, which gives the factor $\tfrac12$ in $w'$. With $I_c=\rho_A^*I_m$, $\kappa=B_{\mathrm{DH}}\sqrt{I_m}$ and $N_A w'/RT$ becomes the displayed formula.

## Sources

- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 10.4, Eqs. 10.4.1, 10.4.3 and 10.4.4. [Section 10.4](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/10%3A_Electrolyte_Solutions/10.04%3A_The_Debye-Huckel_Theory)
- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 10.5, Eq. 10.5.4 and the final step to Eq. 10.4.1. [Section 10.5](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/10%3A_Electrolyte_Solutions/10.05%3A_Derivation_of_the_Debye-Huckel_Theory)
