# Half-saturating total ligand under depletion

With receptor depletion of ligand, the total ligand concentration giving half-maximal receptor occupancy is $K_d+R_T/2$, not $K_d$, and the depletion at that point is $R_T/(2K_d+R_T)$.

**Setting.** As on [exact binding under ligand depletion](exact-binding-under-ligand-depletion.md): one class of sites, total receptor $R_T>0$, total ligand $L_T\ge 0$, dissociation constant $K_d>0$, complex $x$ the unique admissible root, and, for $L_T>0$, depletion $\delta=x/L_T$.

**Statement.**

1. Half occupancy $x=R_T/2$ holds if and only if $L_T=\mathrm{EC}_{50}$, where

$$\mathrm{EC}_{50}=K_d+\frac{R_T}{2}.$$

2. At that point the free ligand equals $K_d$ and the depletion is

$$\delta\big|_{L_T=\mathrm{EC}_{50}}=\frac{R_T}{2K_d+R_T}.$$

3. As $L_T\to0^+$ the depletion tends to $R_T/(K_d+R_T)$; the source states that depletion is most pronounced at the lowest ligand concentrations, where its value may be approximated by this expression.

Consequently $K_d=\mathrm{EC}_{50}-R_T/2$, so estimating $K_d$ from a saturation curve under depletion requires $R_T$ as well as $\mathrm{EC}_{50}$, and $\mathrm{EC}_{50}/K_d=1+R_T/(2K_d)$. The source's working guideline is to keep $R_T$ below about $0.1K_d$, which keeps $\mathrm{EC}_{50}$ within 5% of $K_d$.

## Context

Undergraduate to graduate. This is the quantitative reason why apparent affinities measured with concentrated targets (receptor-rich preparations or binding surfaces) shift toward higher ligand.

## Depends on

- [Exact equilibrium binding under ligand depletion](exact-binding-under-ligand-depletion.md)
- [Equilibrium occupancy of one class of independent binding sites](single-class-binding-isotherm.md)

## Proof depends on

None.

## Expansion

Proof: from $K_dx=[R][L]$ with $x=[R]=R_T/2$ one gets $[L]=K_d$, and ligand conservation gives $L_T=K_d+R_T/2$; uniqueness of the admissible root gives the converse. Item 2 is $\delta=(R_T/2)/(K_d+R_T/2)$. For item 3, $x/L_T=x/([L]+x)$ and $[L]=K_dx/[R]$ give $\delta=[R]/(K_d+[R])$, and $[R]\to R_T$ as $L_T\to0^+$.

Derived here and not stated in the cited source (a candidate separate page): since $[R]$ decreases strictly as $L_T$ increases, $\delta$ is strictly decreasing with unattained supremum $R_T/(K_d+R_T)$; hence the supremum is below 10% iff $R_T<K_d/9$, depletion is below 10% at every $L_T>0$ iff $R_T\le K_d/9$, and depletion at the half-saturation point is below 10% iff $R_T<2K_d/9$, so the guideline $R_T<0.1K_d$ is a slightly conservative sufficient condition.

Remaining decomposition before the page can be marked ready: a lemma that the admissible root $x$ is strictly increasing in $L_T$ (from implicit differentiation of the quadratic, or from monotonicity of the rationalized formula), and a source for the exact thresholds before they enter a statement.

## Sources

- E. C. Hulme and M. A. Trevethick, "Ligand binding assays at equilibrium: validation and interpretation", *British Journal of Pharmacology* 161(6) (2010), 1219–1237, [doi.org](https://doi.org/10.1111/j.1476-5381.2009.00604.x); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC3000649/), section "The effect of radioligand depletion on tracer association and equilibrium binding" (text statements: depletion is most pronounced at low ligand and approximated there by $[R_T]/(K_d+[R_T])$; $\mathrm{EC}_{50}=K_d+[R_T]/2$; $\delta=[R_T]/(2K_d+[R_T])$ at the $\mathrm{EC}_{50}$; the guideline that depletion be held below 10%, "this means that $[R_T]<0.1K_d$"; $K_d=\mathrm{EC}_{50}-[R_T]/2$).
