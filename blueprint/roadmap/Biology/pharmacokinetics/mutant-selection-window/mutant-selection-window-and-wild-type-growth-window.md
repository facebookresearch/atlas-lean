# Mutant selection window and wild-type growth window

Let $D \ge 0$ be the drug concentration. The basic reproductive ratio of the wild-type virus follows the Hill dose–response curve

$$R_0(D) = \frac{R_{00}}{1 + (D/\mathrm{IC}_{50})^{m}},$$

with drug-free fitness $R_{00} > 1$, half-inhibitory concentration $\mathrm{IC}_{50} > 0$ and slope $m > 0$. A single-point resistant mutant has

$$R_0'(D) = \frac{R_{00}(1-s)}{1 + \big(D/(\rho\, \mathrm{IC}_{50})\big)^{m(1+\sigma)}},$$

where $0 < s < 1$ is the fitness cost of the mutation without drug, $\rho > 1$ the fold change in $\mathrm{IC}_{50}$ and $\sigma \in (-1, 0]$ the fractional change in slope (many mutations reduce the slope). A strain grows when its $R_0 > 1$, and the strain with the larger $R_0$ outcompetes the other. Define

- the **wild-type growth window** $\mathrm{WGW} = \{D : R_0(D) > 1\}$, where therapy fails without resistance;
- the **mutant selection window** $\mathrm{MSW} = \{D : R_0'(D) > R_0(D) \text{ and } R_0'(D) > 1\}$, where a resistant mutant, if present, grows and outcompetes the wild type.

Above the MSW both strains are suppressed. As concentrations decay after the last dose, the system passes through up to four ranges: both suppressed, MSW only, the overlap of MSW and WGW (failure possible without resistance but hastened by the mutant), and WGW with the wild type fitter. Successful therapy must both minimize time in the MSW and delay entry into the WGW, two goals in tension, since a shorter half-life shortens the first but hastens the second.

## Depends on

- [Baseline-plus-increment Hill response](../pharmacodynamic-response-models/response.md)

## Expansion

The model summarizes the viral life cycle by $R_0$ and makes drug effect multiplicative on it. Resistance acts through $\rho$ and $\sigma$: raising $\mathrm{IC}_{50}$ shifts the mutant curve right, lowering the slope flattens it, and the cost lowers its plateau, so the mutant is less fit than the wild type at low concentrations but fitter at high ones. Applied to 66 drug–mutation pairs, the windows explain class differences in HIV therapy: non-nucleoside reverse transcriptase inhibitors, with long half-lives, rarely enter the WGW but spend long in the MSW, while boosted protease inhibitors, with steep slopes and short half-lives, spend little time in the MSW but enter the WGW quickly after missed doses, which explains failure without protease-inhibitor resistance.

## Sources

- D. I. S. Rosenbloom, A. L. Hill, S. A. Rabi, R. F. Siliciano and M. A. Nowak, "Antiretroviral dynamics determines HIV evolution and predicts therapy outcome", Nature Medicine 18 (2012), Results ("Defining the mutant selection window", Equations 1–2, Figure 1), <https://doi.org/10.1038/nm.2892>, PMCID: PMC3490032.
