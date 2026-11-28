# Polychromatic deviation from Beer's law

If the light reaching the sample contains two wavelengths at which the analyte has different molar absorptivities, the measured absorbance is $-\log_{10}$ of the summed transmitted power over the summed incident power, which is not proportional to concentration; for two different absorptivities the source describes a negative deviation from Beer's law (absorbance smaller than expected).

**Setting.** Radiation with fixed incident powers $P_0'>0$ and $P_0''>0$ at two wavelengths passes through path length $b>0$ of an analyte at concentration $C\ge0$ with molar absorptivities $\varepsilon',\varepsilon''$; each wavelength obeys the [Beer–Lambert law](beer-lambert-law.md), $P_T=P_0\,10^{-\varepsilon bC}$, and the detector measures the total powers.

**Statement.** The measured absorbance is

$$A(C)=-\log_{10}\frac{P_T'+P_T''}{P_0'+P_0''}=-\log_{10}\frac{P_0'\,10^{-\varepsilon' bC}+P_0''\,10^{-\varepsilon'' bC}}{P_0'+P_0''}.$$

If $\varepsilon'=\varepsilon''=\varepsilon$ this reduces to $A=\varepsilon bC$. If $\varepsilon'\neq\varepsilon''$ the source states that the relation deviates from Beer's law and that the absorbance is smaller than expected (a negative deviation); it adds that the deviation is small when the absorptivity is essentially constant over the wavelengths used.

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

- D. Harvey, *Instrumental Analysis*, LibreTexts, Section 13.2 "Beer's Law", subsection "Instrumental Limitations to Beer's Law" (equations labelled IL1 and IL2 and the following paragraph: "the absorbance is smaller than expected" and "Polychromatic radiation always gives a deviation from Beer's law"; read at [chem.libretexts.org](https://chem.libretexts.org/Bookshelves/Analytical_Chemistry/Instrumental_Analysis_%28LibreTexts%29/13:_Introduction_to_Ultraviolet_Visible_Absorption_Spectrometry/13.02:_Beer's_Law)).
