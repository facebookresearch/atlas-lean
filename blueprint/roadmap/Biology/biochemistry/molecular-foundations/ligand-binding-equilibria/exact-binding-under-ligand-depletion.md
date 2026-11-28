# Exact equilibrium binding under ligand depletion

When neither binding partner is in large excess, the equilibrium complex concentration of $R+L\rightleftharpoons RL$ is the smaller root of a quadratic in the total concentrations; the hyperbolic isotherm in total ligand is its limit when the receptor concentration is small.

**Setting.** Total receptor $R_T>0$, total ligand $L_T\ge 0$ and dissociation constant $K_d>0$ (all in M, ideal activities, one class of sites, 1:1 binding). At equilibrium the free concentrations $[R],[L]\ge 0$ and the complex $x=[RL]\ge 0$ satisfy

$$[R]+x=R_T,\qquad [L]+x=L_T,\qquad K_d\,x=[R]\,[L].$$

**Statement.** These equations have exactly one solution with $[R],[L],x\ge 0$. With $S=R_T+L_T+K_d$ it is

$$x=\frac{S-\sqrt{S^2-4R_TL_T}}{2}=\frac{2R_TL_T}{S+\sqrt{(R_T-L_T)^2+K_d\,(K_d+2R_T+2L_T)}},$$

the smaller root of $x^2-Sx+R_TL_T=0$; it lies in $[0,\min(R_T,L_T)]$, and $x=0$ exactly when $L_T=0$. The second (rationalized) form is algebraically equal to the first and avoids subtracting nearly equal numbers in numerical evaluation. The expression is symmetric in $R_T$ and $L_T$: the equations make no distinction between receptor and ligand. The fraction of receptor bound is $x/R_T$, and for $L_T>0$ the ligand depletion is $\delta=x/L_T$. For fixed $L_T$ and $K_d$,

$$\lim_{R_T\to 0^+}\frac{x}{R_T}=\frac{L_T}{K_d+L_T},$$

which is the [single-class isotherm](single-class-binding-isotherm.md) with the free ligand replaced by the total.

This is an exact forward model. Whether $K_d$ can be estimated precisely from data fitted to it is a separate statistical question: both cited sources warn that in the "titration regime" (limiting partner concentrated far above $K_d$) binding data constrain $K_d$ poorly, and that a valid $K_d$ should not change when the limiting component is varied. Those are statements about experimental design and estimation, not consequences of the algebra.

## Context

Undergraduate to graduate. The page is a prerequisite for interpreting binding of nucleic-acid strands or ligands at the micromolar concentrations typical of materials formulations; no specific Artzi result is derived here.

## Depends on

- [Equilibrium occupancy of one class of independent binding sites](single-class-binding-isotherm.md)

## Proof depends on

None.

## Expansion

Proof: eliminating $[R]$ and $[L]$ gives $f(x)=x^2-Sx+R_TL_T=0$. Its discriminant $S^2-4R_TL_T=(R_T-L_T)^2+K_d(K_d+2R_T+2L_T)$ is positive. With $m=\min(R_T,L_T)$ one has $f(0)=R_TL_T\ge 0$ and $f(m)=-K_d\,m\le 0$ (strict when $m>0$), so exactly one root lies in $[0,m]$ and it is the smaller one; the larger root is at least $S/2>m$ and would make a free concentration negative. When $L_T=0$ the roots are $0$ and $R_T+K_d$, so $x=0$. The rationalized form follows from multiplying by $S+\sqrt{\cdot}$; it gives the $R_T\to0^+$ limit directly, since its denominator tends to $2(L_T+K_d)$.

Remaining decomposition before the page can be marked ready: the mass-action model definition shared with the single-class page (see its Expansion), and an explicit statement of which quantities are held fixed in the limit.

## Sources

- I. Jarmoskaite et al., "How to measure and evaluate binding affinities", *eLife* 9 (2020), e57264, [doi.org](https://doi.org/10.7554/eLife.57264); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC7452723/), section "Avoid the titration regime", Eq. 5 (the quadratic binding equation written for the fraction of the limiting RNA bound) and the discussion of the binding, intermediate and titration regimes and of fitting with Eq. 5.
- E. C. Hulme and M. A. Trevethick, "Ligand binding assays at equilibrium: validation and interpretation", *British Journal of Pharmacology* 161(6) (2010), 1219–1237, [doi.org](https://doi.org/10.1111/j.1476-5381.2009.00604.x); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC3000649/), section "The effect of radioligand depletion on tracer association and equilibrium binding", Eq. 3 (rendered as an image; the text states that it solves the conservation equations and makes no formal distinction between receptor and ligand) and the definition of depletion $\delta=[RL]/[L_T]$.
