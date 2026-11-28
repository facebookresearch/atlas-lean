# Debye–Hückel limiting law

As the ionic strength tends to zero, the Debye–Hückel mean ionic activity coefficient satisfies $\ln\gamma_\pm=-A_{\mathrm{DH}}|z_+z_-|\sqrt{I_m}+O(I_m)$: the limiting slope of $\ln\gamma_\pm$ against $\sqrt{I_m}$ is $-A_{\mathrm{DH}}|z_+z_-|$, independent of $a$.

Under the hypotheses of the [Debye–Hückel mean ionic activity coefficient](debye-hueckel-mean-ionic-activity-coefficient.md),

$$\lim_{I_m\to0^+}\frac{\ln\gamma_\pm}{\sqrt{I_m}}=-A_{\mathrm{DH}}|z_+z_-|,\qquad
\Big|\ln\gamma_\pm+A_{\mathrm{DH}}|z_+z_-|\sqrt{I_m}\Big|\le A_{\mathrm{DH}}B_{\mathrm{DH}}\,a\,|z_+z_-|\,I_m .$$

The **limiting law** $\ln\gamma_\pm\approx-A_{\mathrm{DH}}|z_+z_-|\sqrt{I_m}$ is therefore exact to first order in
$\sqrt{I_m}$ and does not depend on the ion-size parameter $a$.

## Context

Graduate physical chemistry; measured $\ln\gamma_\pm$ of HCl and CaCl$_2$ approach the predicted limiting slopes, while the full equation fits a wider range. This is the dilute-electrolyte correction used to extrapolate standard cell potentials to infinite dilution.

## Depends on

- [Debye–Hückel mean ionic activity coefficient](debye-hueckel-mean-ionic-activity-coefficient.md)

## Proof depends on

None.

## Expansion

Write $A=A_{\mathrm{DH}}|z_+z_-|$, $B=B_{\mathrm{DH}}$ and $s=\sqrt{I_m}\ge0$, with $A_{\mathrm{DH}},B_{\mathrm{DH}},a$ fixed. Then $\ln\gamma_\pm=-As/(1+Bas)$ and $-As/(1+Bas)+As=ABas^2/(1+Bas)\in[0,ABas^2]$. Dividing by $s>0$ and letting $s\to0^+$ gives the limit.

## Sources

- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 10.4, Eq. 10.4.7 and the discussion of the limiting law (Eq. 10.4.8) and Fig. 10.4. [Section 10.4](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/10%3A_Electrolyte_Solutions/10.04%3A_The_Debye-Huckel_Theory)
