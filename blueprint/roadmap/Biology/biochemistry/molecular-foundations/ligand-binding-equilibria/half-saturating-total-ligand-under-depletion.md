# Half-saturating total ligand under depletion

With receptor depletion of ligand, the total ligand concentration giving half-maximal receptor occupancy is $K_d+R_T/2$, not $K_d$, and the depletion at that point is $R_T/(2K_d+R_T)$.

**Setting.** As on [exact binding under ligand depletion](exact-binding-under-ligand-depletion.md): one class of sites, total receptor $R_T>0$, total ligand $L_T\ge 0$, dissociation constant $K_d>0$, complex $x$ the unique admissible root, and, for $L_T>0$, depletion $\delta=x/L_T$.

**Statement.**

1. Half occupancy $x=R_T/2$ holds if and only if $L_T=\mathrm{EC}_{50}$, where

$$\mathrm{EC}_{50}=K_d+\frac{R_T}{2}.$$

2. At that point the free ligand equals $K_d$ and the depletion is

$$\delta\big|_{L_T=\mathrm{EC}_{50}}=\frac{R_T}{2K_d+R_T}.$$

3. For every $L_T>0$ the depletion equals $\delta=[R]/(K_d+[R])$, where $[R]=R_T-x$ is the free receptor; it is strictly decreasing in $L_T$ and

$$\sup_{L_T>0}\delta=\lim_{L_T\to 0^+}\delta=\frac{R_T}{K_d+R_T}.$$

Consequently $K_d=\mathrm{EC}_{50}-R_T/2$, so estimating $K_d$ from a saturation curve under depletion requires $R_T$ as well as $\mathrm{EC}_{50}$, and $\mathrm{EC}_{50}/K_d=1+R_T/(2K_d)$. The supremum of the depletion is below 10% if and only if $R_T<K_d/9$; depletion is below 10% at every $L_T>0$ if and only if $R_T\le K_d/9$ (at $R_T=K_d/9$ the supremum $10\%$ is approached as $L_T\to0^+$ but not attained); and depletion at the half-saturation point is below 10% if and only if $R_T<2K_d/9$. The source's working guideline $R_T<0.1K_d$ is therefore a sufficient (slightly conservative) condition for depletion below 10% everywhere, and it keeps $\mathrm{EC}_{50}$ within 5% of $K_d$.

## Context

Undergraduate to graduate. This is the quantitative reason why apparent affinities measured with concentrated targets (receptor-rich preparations or binding surfaces) shift toward higher ligand. No Artzi-specific result is claimed.

## Depends on

- [Exact equilibrium binding under ligand depletion](exact-binding-under-ligand-depletion.md)
- [Equilibrium occupancy of one class of independent binding sites](single-class-binding-isotherm.md)

## Proof depends on

None.

## Expansion

Proof: from $K_dx=[R][L]$ with $x=[R]=R_T/2$ one gets $[L]=K_d$, and ligand conservation gives $L_T=K_d+R_T/2$; uniqueness of the admissible root gives the converse. Item 2 is $\delta=(R_T/2)/(K_d+R_T/2)$. For item 3, $x/L_T=x/([L]+x)$ and $[L]=K_dx/[R]$ give $\delta=[R]/(K_d+[R])$; $[R]$ decreases strictly as $L_T$ increases (more ligand binds more receptor), and $[R]\to R_T$ as $L_T\to0^+$. The supremum condition is $R_T/(K_d+R_T)<1/10$; since $[R]<R_T$ for every $L_T>0$, the supremum is not attained, which gives the non-strict pointwise condition $R_T/(K_d+R_T)\le1/10$; the half-point condition is $R_T/(2K_d+R_T)<1/10$.

Remaining decomposition before the page can be marked ready: a lemma that the admissible root $x$ is strictly increasing in $L_T$ (from implicit differentiation of the quadratic, or from monotonicity of the rationalized formula), which item 3 uses.

## Sources

- E. C. Hulme and M. A. Trevethick, "Ligand binding assays at equilibrium: validation and interpretation", *British Journal of Pharmacology* 161(6) (2010), 1219–1237, [doi.org](https://doi.org/10.1111/j.1476-5381.2009.00604.x); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC3000649/), section "The effect of radioligand depletion on tracer association and equilibrium binding" (text statements: depletion is most pronounced at low ligand and approximated there by $[R_T]/(K_d+[R_T])$; $\mathrm{EC}_{50}=K_d+[R_T]/2$; $\delta=[R_T]/(2K_d+[R_T])$ at the $\mathrm{EC}_{50}$; the guideline that depletion be held below 10%, "this means that $[R_T]<0.1K_d$"; $K_d=\mathrm{EC}_{50}-[R_T]/2$).
