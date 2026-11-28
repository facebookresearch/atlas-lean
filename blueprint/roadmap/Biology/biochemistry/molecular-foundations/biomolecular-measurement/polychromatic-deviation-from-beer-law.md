# Polychromatic deviation from Beer's law

If the light reaching the sample contains two wavelengths at which the analyte has different molar absorptivities, the measured absorbance, $-\log_{10}$ of summed transmitted over summed incident power, is not proportional to concentration: with both wavelengths carrying positive power and $b>0$, the source describes a deviation from Beer's law, smaller when the two absorptivities are nearly equal.

**Setting.** Radiation with fixed incident powers $P_0'>0$ and $P_0''>0$ at two wavelengths passes through path length $b>0$ of an analyte at concentration $C\ge0$ with molar absorptivities $\varepsilon',\varepsilon''$; each wavelength obeys the [Beer–Lambert law](beer-lambert-law.md), $P_T=P_0\,10^{-\varepsilon bC}$, and the detector measures the total powers.

**Statement.** The measured absorbance is

$$A(C)=-\log_{10}\frac{P_T'+P_T''}{P_0'+P_0''}=-\log_{10}\frac{P_0'\,10^{-\varepsilon' bC}+P_0''\,10^{-\varepsilon'' bC}}{P_0'+P_0''}.$$

If $\varepsilon'=\varepsilon''=\varepsilon$ this reduces to $A=\varepsilon bC$. For the two-wavelength formula the source states that it "predicts that the absorbance is smaller than expected if $\epsilon^{\prime} > \epsilon^{\prime\prime}$", and that the effect "is smaller if the value of $\varepsilon$ essentially is constant" over the wavelengths passed; for exactly equal absorptivities there is no deviation, as shown above.

## Context

Undergraduate instrumental analysis. This is why absorbance is best measured at the top of a broad band and with an effective bandwidth small compared with the absorber's natural bandwidth (practical guidance from the source). It applies to any absorbance-based quantification of biomolecules.

## Depends on

- [Beer–Lambert law and additivity of absorbance](beer-lambert-law.md)

## Proof depends on

None.

## Expansion

Proof: each wavelength contributes $P_T=P_0\,10^{-\varepsilon bC}$, and the absorbance of the summed beam is the definition applied to total powers; with equal absorptivities the common factor $10^{-\varepsilon bC}$ comes out of the sum. **Typographical note:** the source's displayed Eq. IL2 writes $10^{-\epsilon bC}$ in both terms, which would give a straight line; the derivation requires $\varepsilon'$ and $\varepsilon''$ respectively, as in the source's preceding equations and as used above.

Remaining decomposition before the page can be marked ready: (i) a separately sourced page for the shape of $A(C)$ (its concavity, the tangent bound and the decrease of $A(C)/C$, which follow from log-sum-exp calculus but are not stated in the cited section); (ii) the detector model (summed powers with fixed weights) stated as an explicit hypothesis on a definition page.

## Sources

- D. Harvey, *Instrumental Analysis*, LibreTexts, Section 13.2 "Beer's Law", subsection "Instrumental Limitations to Beer's Law" (equations labelled IL1 and IL2 and the following paragraph: IL2 "predicts that the absorbance is smaller than expected if" $\epsilon^{\prime}>\epsilon^{\prime\prime}$, and its general remark "Polychromatic radiation always gives a deviation from Beer's law", which is quoted here only as the source's wording and does not cover the equal-absorptivity case, where the two-wavelength formula is exactly linear; read at [chem.libretexts.org](https://chem.libretexts.org/Bookshelves/Analytical_Chemistry/Instrumental_Analysis_%28LibreTexts%29/13:_Introduction_to_Ultraviolet_Visible_Absorption_Spectrometry/13.02:_Beer's_Law)).
