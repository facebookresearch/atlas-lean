# Beer–Lambert law and additivity of absorbance

For monochromatic light passing through a dilute absorbing solution, the absorbance $A=-\log_{10}(P_T/P_0)$ is proportional to path length and concentration, $A=\varepsilon bC$, and the absorbances of independently absorbing species add: $A=b\sum_i\varepsilon_iC_i$.

**Model.** Radiation of a single wavelength with incident power $P_0>0$ passes through a sample of path length $b\ge0$; the transmitted power is $P_T>0$ (powers corrected against a blank), the transmittance $T=P_T/P_0$ and the absorbance $A=-\log_{10}T$. For an absorbing species at molar concentration $C\ge0$ with molar absorptivity $\varepsilon$ at that wavelength (units M$^{-1}$cm$^{-1}$ when $b$ is in cm),

$$A=-\log_{10}\frac{P_T}{P_0}=\varepsilon\,b\,C,\qquad\text{equivalently}\qquad P_T=P_0\,10^{-\varepsilon bC}.$$

For a mixture of $n$ species that absorb independently, each at its own concentration $C_i$ with fixed $\varepsilon_i$,

$$\frac{P_T}{P_0}=\prod_{i=1}^{n}10^{-\varepsilon_i bC_i},\qquad A_{\mathrm{mix}}=\sum_{i=1}^{n}\varepsilon_i\,b\,C_i.$$

**Status and limitations.** The law is a limiting model. The source distinguishes three kinds of deviation. *Fundamental:* at higher concentrations absorbers interact and the refractive index changes, so $\varepsilon$ is not constant; the law is valid at low concentration. *Chemical:* if the absorbing species take part in a concentration-dependent equilibrium, absorbance is still additive over the actual species concentrations, and it is linear in the analytical (total) concentration whenever the absorptivity averaged over the species, $\sum_i\varepsilon_iC_i/\sum_iC_i$, stays constant; fixed speciation is a sufficient condition (so are equal absorptivities of interconverting species). *Instrumental:* stray light and non-monochromatic radiation produce deviations that follow from the attenuation model itself; the polychromatic case is treated on [polychromatic deviation from Beer's law](polychromatic-deviation-from-beer-law.md).

## Context

Undergraduate analytical chemistry and biochemistry. Absorbance at 260 and 280 nm is the routine way to quantify nucleic acids and proteins, and a Beer's-law calibration line is inverted to estimate unknown concentrations ([inverse prediction from a calibration line](../../../../Chemistry/analytical-chemistry/analytical-calibration-and-inverse-prediction/inverse-prediction.md)). The main text of the Artzi RNA-triple-helix study reports that absorbance spectra of the RNA strands alone and assembled into duplexes and the triplex were recorded (Conde et al. 2016, Results; the spectra are in its supplementary information, which was not accessed); such spectra are context, not a test of this law.

## Depends on

None.

## Proof depends on

- [Beer–Lambert transmission multiplies across finitely many layers](../../../../EarthScience/atmosphere-and-climate/optical-depth-and-transmission/transmission-mul-layers.md)

## Expansion

The single-species law is the model's defining proportionality (a definition plus an empirical validity range). The mixture statement follows from it: if each species attenuates independently, its optical depth is $\tau_i=\varepsilon_ibC_i\ln10$, and the existing result that transmission multiplies across layers, $\exp(-\sum_i\tau_i)=\prod_i\exp(-\tau_i)$, gives the product form and hence additivity of $A$. A first-principles derivation assumes that each thin layer absorbs a fraction of the incident power proportional to the number of absorbers it contains, $dP/dx=-kCP$, giving $\varepsilon=k/\ln10$.

Remaining decomposition before the page can be marked ready: (i) a definition page for the attenuation model with species-wise optical depths $\tau_i=\varepsilon_ibC_i\ln10$ and the independence hypothesis, linking the optical-depth pages; (ii) explicit hypotheses $P_0,P_T>0$ and monochromatic radiation; (iii) the deviation categories kept as model-scope statements, not as theorems.

## Sources

- D. Harvey, *Instrumental Analysis*, LibreTexts, Section 13.2 "Beer's Law" (read at [chem.libretexts.org](https://chem.libretexts.org/Bookshelves/Analytical_Chemistry/Instrumental_Analysis_%28LibreTexts%29/13:_Introduction_to_Ultraviolet_Visible_Absorption_Spectrometry/13.02:_Beer's_Law)), subsections "Absorbance and Concentration" ($A=-\log T$, $A=\varepsilon bC$), "Beer's Law and Multicomponent Samples" ($A_{\mathrm{tot}}$ and $A_{\mathrm{mix}}$) and "Limitations to Beer's Law" (fundamental, chemical and instrumental limitations).
- J. Conde, N. Oliva, M. Atilano, H. S. Song and N. Artzi, "Self-assembled RNA-triple-helix hydrogel scaffold for microRNA modulation in the tumour microenvironment", *Nature Materials* 15(3) (2016), 353–363, [doi.org](https://doi.org/10.1038/nmat4497); author manuscript read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC6594154/), Results (main text only; context).
