# Solubility–diffusion permeation of small nonelectrolytes across lipid bilayers

Small uncharged molecules can cross lipid bilayers by dissolving in the hydrocarbon interior and diffusing through it; in the homogeneous-slab model their permeability is the membrane–water partition coefficient times the membrane diffusion coefficient divided by the thickness, and measurements on synthetic bilayers are consistent with this picture, though water and urea deviate from the empirical scaling.

**Model (conditional).** In the solubility–diffusion model a neutral solute permeates a homogeneous membrane slab of thickness $a>0$ by steady one-dimensional diffusion with constant membrane diffusion coefficient $D_m>0$, with equilibrium partitioning (partition coefficient $\beta>0$, equal at both faces) between membrane interior and water. The outward flux is then $J=(\beta D_m/a)\,\Delta c$ with $\Delta c=c_{\mathrm{in}}-c_{\mathrm{out}}$ (SI: $J$ in mol m$^{-2}$s$^{-1}$, $P$ in m s$^{-1}$), so the permeability is $P=\beta D_m/a$. Within this model, raising $\beta$ at fixed $D_m$ and $a$ raises $P$. The same structure appears in the Hodgkin–Katz definition of ionic permeability used in the [GHK current equation](goldman-hodgkin-katz-current-equation.md).

**Evidence (empirical).** Finkelstein measured, for planar bilayers of lecithin, lecithin:cholesterol and sphingomyelin:cholesterol, the diffusional permeability $P_d$ of water and seven nonelectrolytes (1,6-hexanediol, 1,4-butanediol, n-butyramide, isobutyramide, acetamide, formamide, urea) and their n-hexadecane:water partition coefficients $K_{\mathrm{hc}}$ (written $K_{nc}$ in the source). The abstract reports:

- for a given membrane composition, $P_d/(D\,K_{\mathrm{hc}})$, with $D$ the diffusion coefficient in **water** (not in the membrane), is about the same for most molecules tested, and there is no extraordinary dependence of $P_d$ on molecular weight;
- the main exceptions to this scaling are water, whose ratio is about 10-fold larger than average, and urea, about 5-fold smaller;
- absolute permeabilities change by more than a factor of 100 from the tightest (sphingomyelin:cholesterol) to the loosest (lecithin) membrane while relative values stay roughly constant, and the tight membrane discriminates between straight and branched isomers ($P_d$(n-butyramide)$/P_d$(isobutyramide)$=2.5$).

The author concludes that water and nonelectrolytes cross these bilayers by a solubility–diffusion mechanism, with an interior more like an oil than a rubber-like polymer. These are empirical findings for synthetic bilayers under the study's conditions; the exceptions are departures from the empirical scaling, not proof of a specific alternative mechanism, and the findings do not by themselves predict permeation across cell membranes, which contain proteins, channels and transporters, or of large conjugates such as lipid-modified RNA.

## Context

Undergraduate to graduate membrane biophysics. The solubility–diffusion picture (Overton's rule) is the usual starting point for thinking about passive membrane permeation of small molecules. In the Artzi laboratory's RNA-triple-helix work, one RNA strand carries a cholesterol conjugate stated to "facilitate the permeation of cell membranes", improve co-transfection and protect oligonucleotides (Conde et al. 2016, Results, citing earlier literature); that design rationale was not tested against this model, and the model does not establish it.

## Depends on

None. The items above are empirical or conditional on the stated slab model; the GHK current page is linked for the analogous ionic definition, not as a proof of the experiment.

## Proof depends on

None.

## Expansion

Remaining decomposition before any statement here can become a theorem page: (i) a definition page for steady one-dimensional Fick diffusion in a homogeneous slab with interface partitioning, on which $P=\beta D_m/a$ is a lemma; (ii) the abstract's common ratio constrains only the combination $(\beta/K_{\mathrm{hc}})(D_m/D)/a$; separate solute-independent proportionality of $\beta$ to $K_{\mathrm{hc}}$ and of $D_m$ to $D$ would be sufficient for it but is not implied, and the water and urea deviations show the common ratio fails for some molecules; (iii) an uncertainty decomposition covering measurement error in $P_d$ (unstirred layers), the choice of reference solvent for partitioning, and membrane heterogeneity. Only the abstract of Finkelstein's paper was accessible as text, so the numbers above are restricted to what the abstract states.

## Sources

- A. Finkelstein, "Water and nonelectrolyte permeability of lipid bilayer membranes", *Journal of General Physiology* 68(2) (1976), starting page 127; abstract read at [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC2228420/) (full text available only as a scanned PDF, not read); all claims restricted to the abstract.
- O. Alvarez and R. Latorre, "The enduring legacy of the 'constant-field equation' in membrane ion transport", *Journal of General Physiology* 149(10) (2017), 911–920; open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC5688357/), Eq. 17 (Hodgkin–Katz permeability), Appendix A (diffusion-coefficient form) and the assumption that boundary concentrations are proportional to bath concentrations.
- J. Conde, N. Oliva, M. Atilano, H. S. Song and N. Artzi, "Self-assembled RNA-triple-helix hydrogel scaffold for microRNA modulation in the tumour microenvironment", *Nature Materials* 15(3) (2016), 353–363, [doi.org](https://doi.org/10.1038/nmat4497); author manuscript read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC6594154/), Results (cholesterol-conjugated miR-205 sense strand).
