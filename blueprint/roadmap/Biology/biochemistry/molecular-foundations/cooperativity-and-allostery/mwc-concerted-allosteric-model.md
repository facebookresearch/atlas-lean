# Monod–Wyman–Changeux concerted allosteric model

In the MWC model an oligomer with $n$ identical sites switches all its subunits together between a relaxed and a tense conformation of possibly different affinity; its weight sum relative to the unliganded relaxed state is $(1+\alpha)^n+L(1+c\alpha)^n$, and for suitable parameters it gives sigmoidal saturation without direct site–site interaction energies.

**Definition.** Consider an oligomer with $n\ge1$ identical ligand sites that exists in two conformations, $R$ (relaxed) and $T$ (tense), with these assumptions: all subunits change conformation together (concerted transition); within each conformation the sites bind independently with finite intrinsic dissociation constants $K_R,K_T>0$; in the absence of ligand the conformations are in equilibrium with allosteric constant

$$L=\frac{[T_0]}{[R_0]}=e^{-\beta(\varepsilon_T-\varepsilon_R)}>0,$$

where $\varepsilon_R,\varepsilon_T$ are the molecular free energies of the unliganded conformations, $T>0$ and $\beta=1/k_BT$ (with molar free energies use $1/RT$). With free ligand concentration $x\ge0$ write

$$\alpha=\frac{x}{K_R},\qquad c=\frac{K_R}{K_T}>0,$$

so that $c\alpha=x/K_T$ (the classical labelling takes $0<c\le1$, so $R$ has the higher affinity). Relative to $[R_0]$, the $i$-liganded species have weights $\binom{n}{i}\alpha^i$ in $R$ and $L\binom{n}{i}(c\alpha)^i$ in $T$, so the weight sum, fractional saturation and fraction of molecules in $R$ are

$$Z(\alpha)=(1+\alpha)^n+L(1+c\alpha)^n,$$

$$Y(\alpha)=\frac{\alpha(1+\alpha)^{n-1}+Lc\alpha(1+c\alpha)^{n-1}}{(1+\alpha)^n+L(1+c\alpha)^n},\qquad p_R(\alpha)=\frac{(1+\alpha)^n}{(1+\alpha)^n+L(1+c\alpha)^n}.$$

$Z(0)=1+L$; dividing by $1+L$ gives the normalized [Adair binding polynomial](adair-binding-polynomial.md) with $\beta_i=\binom ni\big(K_R^{-i}+L\,K_T^{-i}\big)/(1+L)$. Saturation $Y$ and the relaxed fraction $p_R$ are different observables; $p_R$ is an activity curve only under the additional readout assumption that $R$ is active and $T$ inactive.

**Source of the formulas.** Marzen, Garcia and Phillips give the activity of an MWC molecule with $n$ sites (their Eq. 8, with active and inactive states corresponding to $R$ and $T$ here), and their Fig. 2(c) caption defines the conformational constant as $L=e^{-\beta\Delta\varepsilon}$ with $\Delta\varepsilon=\varepsilon_I-\varepsilon_A$, the convention used above. The weights, $Z$, $p_R$ and $Y$ follow from these by direct computation (their two-site binding and activity forms are their Eqs. 11 and 14).

**Shape.** Whether the saturation curve is sigmoidal depends on the parameters; it is not automatic. A sigmoid on a linear concentration axis and a local Hill slope above one are related but distinct criteria. Within each conformation sites do not interact directly, but occupancies are correlated through the shared conformation.

## Context

Undergraduate to graduate. MWC is the standard mechanistic model of allostery (hemoglobin, ligand-gated channels, chemoreceptor clusters) and a reference model for cooperative molecular switches.

## Depends on

- [Adair binding polynomial and fractional saturation](adair-binding-polynomial.md)

## Proof depends on

None.

## Expansion

This page is a definition. $Y=\frac{\alpha}{n}\,d\ln Z/d\alpha$ follows from [the logarithmic-derivative identity](mean-occupancy-as-logarithmic-derivative.md) with $\sum_ii\binom{n}{i}y^i=ny(1+y)^{n-1}$. Limiting cases are on [limiting behaviour of the MWC model](limiting-behaviour-of-the-mwc-model.md).

Derived here and not stated in the cited sources (numerical checks of the shape remark): for $n=2$, $L=100$, $c=0.01$ the second difference of $Y$ in $\alpha$ is positive at $\alpha=0.5$ (sigmoidal), while for $n=2$, $L=1$, $c=1/2$ it is negative at every tested $\alpha\ge0$ (concave).

Remaining decomposition before the page can be marked ready: (i) a lemma deriving the binomial weights from independence within each conformation and the concerted constraint; (ii) a lemma identifying the normalized Adair coefficients; (iii) if the shape statements are to be kept as results, an explicit criterion (sign of the second derivative of $Y$ near $\alpha=0$ in terms of $n,L,c$) on its own page.

## Sources

- S. Marzen, H. G. Garcia and R. Phillips, "Statistical mechanics of Monod–Wyman–Changeux (MWC) models", *Journal of Molecular Biology* (2013); author manuscript read at [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC3786005/), section "States and weights in the MWC setting", Eq. 2 (Boltzmann weights of active and inactive states), Fig. 2(c) caption ("$L = e^{-\beta\Delta\varepsilon}$ is the conformational equilibrium constant where $\Delta\varepsilon = \varepsilon_I - \varepsilon_A$"), Eq. 8 (activity with $n$ binding sites) and Eqs. 11 and 14 (two-site binding and activity forms).
- H. Jakubowski and P. Flatt, *Fundamentals of Biochemistry*, LibreTexts, Section 5.11 "Derivation of the MWC Equation" (teaching reference only: the page states that it was written largely with an AI model, and nothing here rests on it alone), Eq. 1 and Steps 1–3 (weights $\binom{n}{i}\alpha^i$ and $L\binom{n}{i}(c\alpha)^i$ relative to $[R_0]$, binding polynomial, fractional saturation, $L=[T_0]/[R_0]$), [bio.libretexts.org](https://bio.libretexts.org/Bookshelves/Biochemistry/Fundamentals_of_Biochemistry_%28Jakubowski_and_Flatt%29/01%3A_Unit_I-_Structure_and_Catalysis/05%3A_Protein_Function/5.11%3A_Derivation_of_the_MWC_Equation).
- M. I. Stefan and N. Le Novère, "Cooperative binding", *PLoS Computational Biology* 9(6) (2013), e1003106, [doi.org](https://doi.org/10.1371/journal.pcbi.1003106), section "The MWC Model" (assumptions of the concerted model; equations rendered as images).
