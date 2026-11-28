# Adair binding polynomial and fractional saturation

For a macromolecule with $N$ ligand sites, the binding polynomial $P(x)=\sum_{i=0}^N\beta_ix^i$ in the free ligand concentration $x$, built from the overall association constants $\beta_i$ of the $i$-liganded species with $\beta_0=1$, gives every species fraction and the Adair fractional saturation $Y=\frac1N\sum_i i\beta_ix^i/P(x)$.

**Definition.** Let a macromolecule $P$ have $N\ge1$ sites for a ligand $X$, and let $PX_i$ denote all species with exactly $i$ ligands bound, summed over which sites are occupied. The overall (cumulative, macroscopic) association constants $\beta_i\ge0$ (units M$^{-i}$) are the equilibrium parameters for which, at every free ligand concentration $x=[X]>0$ and with ideal activities,

$$[PX_i]=\beta_i\,[P]\,x^i\quad(i=0,\dots,N),\qquad \beta_0=1,\qquad \beta_N>0,$$

where $[P]=[PX_0]>0$ is the unliganded concentration. The **binding polynomial** and **species fractions** are

$$P(x)=\sum_{i=0}^{N}\beta_ix^i,\qquad p_i(x)=\frac{\beta_ix^i}{P(x)}\qquad(x\ge0),$$

extended to $x=0$ by the same formulas (so $p_0(0)=1$). Then $P(x)\ge1$, $p_i\ge0$ and $\sum_ip_i=1$. The mean number of bound ligands and the **fractional saturation** (the Adair equation) are

$$\langle i\rangle(x)=\sum_{i=0}^{N}i\,p_i(x),\qquad Y(x)=\frac{\langle i\rangle(x)}{N}=\frac{1}{N}\,\frac{\sum_{i=1}^{N}i\,\beta_ix^i}{1+\sum_{i=1}^{N}\beta_ix^i}.$$

The **stepwise** (Klotz) constants $K_i=\beta_i/\beta_{i-1}$ are defined only when $\beta_{i-1}>0$; the stepwise parametrization is equivalent to the cumulative one exactly when $\beta_1,\dots,\beta_{N-1}>0$ (a model with vanishing intermediate coefficients need not admit a full stepwise parametrization: in the all-or-none case with $N\ge2$, $K_1=0$ and the later quotients are undefined).

**Special cases.** For $N$ identical independent sites with site association constant $K>0$, $\beta_i=\binom{N}{i}K^i$, so $P(x)=(1+Kx)^N$ and $Y=Kx/(1+Kx)$, the [single-class isotherm](../ligand-binding-equilibria/single-class-binding-isotherm.md). The [Monod–Wyman–Changeux model](mwc-concerted-allosteric-model.md) is the case

$$P_{\mathrm{Adair}}(\alpha)=\frac{(1+\alpha)^n+L(1+c\alpha)^n}{1+L},$$

normalized so that $P_{\mathrm{Adair}}(0)=1$; the MWC page's weight sum $(1+\alpha)^n+L(1+c\alpha)^n$ is referenced to the relaxed unliganded state instead, and the species fractions are unchanged by this constant factor. The polynomial plays the role of a partition function of the ligation states, in analogy with the [partition function of a finite system](../../../../Chemistry/chemical-thermodynamics/canonical-ensemble-of-a-finite-system/partition-function.md).

## Context

Undergraduate to graduate biochemistry. Adair introduced stepwise constants to describe hemoglobin's four-site oxygen binding; the binding polynomial is the common language in which phenomenological (Adair, Hill) and mechanistic (MWC, KNF) cooperativity models are compared. Artzi's RNA-triple-helix design assembles three chemically distinct strands at a defined 1:1:1 stoichiometry (Conde et al. 2016); the binding polynomial for one ligand species is at most an analogy for that multi-component assembly, which the paper does not analyze this way.

## Depends on

None.

## Proof depends on

None.

## Expansion

This page is a definition; the facts used are $P(x)\ge\beta_0=1>0$, hence $p_i\ge0$ and $\sum_ip_i=1$, and $Y(x)\to1$ as $x\to\infty$ because $\beta_N>0$. The identity $\langle i\rangle=x\,P'(x)/P(x)$ is on [mean occupancy as a logarithmic derivative](mean-occupancy-as-logarithmic-derivative.md).

Remaining decomposition before the page can be marked ready: (i) a page relating cumulative, stepwise and microscopic (site) constants through statistical factors; (ii) a statement that the $\beta_i$ are well defined from equilibrium data at $x>0$ (independent of the chosen $x$), which is a modelling hypothesis of ideal mass action rather than a theorem.

## Sources

- M. I. Stefan and N. Le Novère, "Cooperative binding", *PLoS Computational Biology* 9(6) (2013), e1003106, [doi.org](https://doi.org/10.1371/journal.pcbi.1003106); journal HTML read at [journals.plos.org](https://journals.plos.org/ploscompbiol/article?id=10.1371/journal.pcbi.1003106), sections "The Adair Equation" (fractional occupancy for four sites and for $n$ sites with combined association constants $K_i$ for binding $i$ ligands) and "The Klotz Equation" (stepwise constants).
- H. Abeliovich, "An empirical extremum principle for the Hill coefficient in ligand-protein interactions showing negative cooperativity", *Biophysical Journal* 89(1) (2005), 76–79, [doi.org](https://doi.org/10.1529/biophysj.105.060194); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC1366580/), section "Theory", Eqs. 1–2 (macroscopic formation constants $K_n$ and the generalized Adair equation, rendered as images; the surrounding text was checked).
- H. Jakubowski and P. Flatt, *Fundamentals of Biochemistry*, LibreTexts, Section 5.11 "Derivation of the MWC Equation", Step 1 (weights relative to the relaxed unliganded state), [bio.libretexts.org](https://bio.libretexts.org/Bookshelves/Biochemistry/Fundamentals_of_Biochemistry_%28Jakubowski_and_Flatt%29/01%3A_Unit_I-_Structure_and_Catalysis/05%3A_Protein_Function/5.11%3A_Derivation_of_the_MWC_Equation).
- J. Conde, N. Oliva, M. Atilano, H. S. Song and N. Artzi, "Self-assembled RNA-triple-helix hydrogel scaffold for microRNA modulation in the tumour microenvironment", *Nature Materials* 15(3) (2016), 353–363, [doi.org](https://doi.org/10.1038/nmat4497); author manuscript read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC6594154/) (context sentence only: assembly at a 1:1:1 molar ratio, Results and Fig. 2).
