# Two-state analysis of chemical denaturation by linear extrapolation

A two-state reading of a denaturation curve converts an optical signal into an unfolded fraction and an apparent free energy at each denaturant concentration; assuming that free energy falls linearly with denaturant concentration, $\Delta G(D)=\Delta G_w-m[D]$, and extrapolating to zero defines the stability in water $\Delta G_w$.

**Model.** A protein unfolds by $N\rightleftharpoons U$ (two-state) at fixed temperature $T>0$ in a denaturant (urea or guanidine hydrochloride) of molar concentration $[D]\ge0$, in a specified solvent and buffer.

1. *Signal decomposition.* At each $[D]$ an observable $y$ (absorbance, fluorescence, circular dichroism, viscosity) is the population-weighted average of native and unfolded contributions $y_N([D])\neq y_U([D])$, which may themselves depend on $[D]$ (sloping baselines):

$$y=f_Ny_N+f_Uy_U,\qquad f_N+f_U=1,\qquad\text{so}\qquad f_U=\frac{y_N-y}{y_N-y_U}.$$

For a valid signal $f_U\in[0,1]$; where $0<f_U<1$ (the transition zone), $K=f_U/(1-f_U)$ and $\Delta G=-RT\ln K$.

2. *Linear extrapolation.* The unfolding free energy is assumed to depend linearly on denaturant concentration over the range studied,

$$\Delta G([D])=\Delta G_w-m\,[D],\qquad m>0\ \ (\text{energy mol}^{-1}\,\text{M}^{-1}),$$

with $\Delta G_w$ (the extrapolated intercept, called the stability in water in the chosen solvent and buffer) and the $m$ value as parameters. Then

$$f_U([D])=\frac{1}{1+\exp\!\big((\Delta G_w-m[D])/RT\big)},$$

and if $\Delta G_w\ge0$ the midpoint $f_U=1/2$ lies at $[D]_{1/2}=\Delta G_w/m\ge0$; it is a physical midpoint only if it falls inside the concentration range where the linear model is assumed. If the affine model is extrapolated to $[D]=0$, a negative intercept predicts more than half unfolded there; this prediction is not a separate measurement.

**Status.** Item 1 follows from the two-state assumption and linear mixing of species signals. Item 2 is an empirical model: its linearity was established by fitting experimental denaturation curves, and $\Delta G_w$ is an extrapolation outside the transition zone. The correlation of $m$ values with the change in solvent-accessible surface area on unfolding is an empirical finding across proteins, not a consequence of the model.

## Context

Undergraduate to graduate biochemistry; the linear extrapolation method is the most widely used way to quote protein stability. Denaturants also probe nucleic-acid assemblies: the main text of an RNA-triple-helix study reports testing triplex stability in the presence of urea, a denaturant of double-stranded RNA (Conde et al. 2016, Results; the data are in its supplementary information, which was not accessed), but the study did not fit the linear extrapolation model, so the relevance here is to the measurement concept only.

## Depends on

- [Two-state unfolding equilibrium and the van 't Hoff slope at the melting temperature](two-state-unfolding-and-the-van-t-hoff-slope.md)

## Proof depends on

None.

## Expansion

Item 1 needs only the two-state model and linear signal mixing at each $[D]$; the logistic form and midpoint in item 2 are algebra under the assumed affine $\Delta G$.

Remaining decomposition before the page can be marked ready: (i) a definition page for the two-state signal model with denaturant-dependent baselines; (ii) a separate page for nonlinear least-squares estimation of $(\Delta G_w,m)$ with explicit noise assumptions, if estimation properties are to be stated; (iii) explicit labelling, on any formal page, that linear dependence on $[D]$, transfer of $\Delta G_w$ to zero denaturant and the surface-area correlation are empirical inputs. Any mechanistic justification of linearity (for example via transfer free energies of exposed groups) is a separate model whose assumptions are empirical.

## Sources

- H. Jakubowski and P. Flatt, *Fundamentals of Biochemistry*, LibreTexts, Section 4.12 "Laboratory Determination of the Thermodynamic Parameters for Protein Denaturation", Eqs. 1–5 (signal decomposition, $K_{eq}=f_D/(1-f_D)$, $\Delta G^0=-RT\ln K_{eq}$) and the learning goals on linear extrapolation to $\Delta G^0_w$ (read at [bio.libretexts.org](https://bio.libretexts.org/Bookshelves/Biochemistry/Fundamentals_of_Biochemistry_%28Jakubowski_and_Flatt%29/01:_Unit_I-_Structure_and_Catalysis/04:_The_Three-Dimensional_Structure_of_Proteins/4.12:_Laboratory_Determination_of_the_Thermodynamic_Parameters_for_Protein_Denaturation)).
- N. Kresge, R. D. Simoni and R. L. Hill, "A new method for estimating protein stability: the work of Nick Pace", *Journal of Biological Chemistry* (JBC Classics, 2008), open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC3258848/) (describes R. F. Greene Jr. and C. N. Pace, *J. Biol. Chem.* 249 (1974), 5388–5393: linear plots of $\Delta G$ against denaturant concentration, intercept as stability and slope as the $m$ value).
- J. K. Myers, C. N. Pace and J. M. Scholtz, "Denaturant m values and heat capacity changes: relation to changes in accessible surface areas of protein unfolding", *Protein Science* 4 (1995), 2138–2148; only the abstract was accessible as text ([pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC2142997/)), which reports the empirical correlation of $m$ with surface area exposed on unfolding ($R=0.84$ for urea, $0.87$ for guanidine hydrochloride); cited for that empirical finding only.
- J. Conde, N. Oliva, M. Atilano, H. S. Song and N. Artzi, "Self-assembled RNA-triple-helix hydrogel scaffold for microRNA modulation in the tumour microenvironment", *Nature Materials* 15(3) (2016), 353–363, [doi.org](https://doi.org/10.1038/nmat4497); author manuscript read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC6594154/), Results (main text only; context).
