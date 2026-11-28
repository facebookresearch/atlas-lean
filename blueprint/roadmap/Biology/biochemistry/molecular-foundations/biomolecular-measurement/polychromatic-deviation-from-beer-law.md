# Polychromatic deviation from Beer's law

If the light reaching the sample contains two wavelengths at which the analyte has different molar absorptivities, the measured absorbance is not proportional to concentration: for positive path length it is a strictly concave function of concentration lying below the line with the incident-power-weighted mean absorptivity, a negative deviation from Beer's law.

**Setting.** Radiation with fixed incident powers $P_0'>0$ and $P_0''>0$ at two wavelengths (or detector-response-weighted powers) passes through path length $b>0$ of an analyte at concentration $C\ge0$ with molar absorptivities $\varepsilon',\varepsilon''$; each wavelength obeys the [Beer–Lambert law](beer-lambert-law.md), $P_T=P_0\,10^{-\varepsilon bC}$, and the detector measures the total powers.

**Statement.** The measured absorbance is

$$A(C)=-\log_{10}\frac{P_T'+P_T''}{P_0'+P_0''}=-\log_{10}\Big(w\,10^{-\varepsilon' bC}+(1-w)\,10^{-\varepsilon'' bC}\Big),\qquad w=\frac{P_0'}{P_0'+P_0''}\in(0,1).$$

If $\varepsilon'=\varepsilon''=\varepsilon$ then $A=\varepsilon bC$. If $\varepsilon'\neq\varepsilon''$ then

$$A'(C)=b\,\bar\varepsilon(C),\qquad A''(C)=-\ln(10)\,b^2\,\operatorname{Var}_C(\varepsilon)<0,$$

where $\bar\varepsilon(C)$ and $\operatorname{Var}_C(\varepsilon)$ are the mean and variance of $\{\varepsilon',\varepsilon''\}$ under the transmitted-power weights $\propto P_0'10^{-\varepsilon'bC}$ and $P_0''10^{-\varepsilon''bC}$. Hence $A$ is strictly concave, $A(0)=0$, $A'(0)=b\,(w\varepsilon'+(1-w)\varepsilon'')$, $A(C)<A'(0)\,C$ for $C>0$, and $A(C)/C$ decreases strictly: a Beer's-law plot bends toward the concentration axis. The source's statement that polychromatic radiation "always" gives a deviation holds exactly when the two absorptivities differ and both wavelengths carry positive weight.

## Context

Undergraduate instrumental analysis. This is why absorbance is best measured at the top of a broad band and with an effective bandwidth small compared with the absorber's natural bandwidth (practical guidance from the source). It applies to any absorbance-based quantification of biomolecules. No Artzi-specific result depends on it.

## Depends on

- [Beer–Lambert law and additivity of absorbance](beer-lambert-law.md)

## Proof depends on

None.

## Expansion

Proof: $A(C)\ln10=-\ln\big(w\,e^{-\varepsilon'bC\ln10}+(1-w)\,e^{-\varepsilon''bC\ln10}\big)$ is minus a log-sum-exp of affine functions of $C$. Differentiating once gives the tilted mean, and twice gives minus $\ln(10)\,b^2$ times the tilted variance, which is positive when $\varepsilon'\neq\varepsilon''$ and $0<w<1$. Strict concavity with $A(0)=0$ gives the tangent bound and the strict decrease of $A(C)/C$ on $C>0$. **Typographical note:** the source's displayed Eq. IL2 writes $10^{-\epsilon bC}$ in both terms, which would give a straight line; the derivation requires $\varepsilon'$ and $\varepsilon''$ respectively, as in the source's preceding equations and as used above.

Remaining decomposition before the page can be marked ready: (i) the derivative formulas for log-sum-exp as a lemma (or a Mathlib reference); (ii) the detector model (summed powers with fixed weights) stated as an explicit hypothesis on a definition page.

## Sources

- D. Harvey, *Instrumental Analysis*, LibreTexts, Section 13.2 "Beer's Law", subsection "Instrumental Limitations to Beer's Law" (equations labelled IL1 and IL2 and the following paragraph on polychromatic radiation; read at [chem.libretexts.org](https://chem.libretexts.org/Bookshelves/Analytical_Chemistry/Instrumental_Analysis_%28LibreTexts%29/13:_Introduction_to_Ultraviolet_Visible_Absorption_Spectrometry/13.02:_Beer's_Law)).
