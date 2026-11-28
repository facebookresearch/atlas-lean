# Competitive binding shift and the Cheng–Prusoff relation

When two ligands compete for the same single class of sites, the competitor raises the apparent dissociation constant of the other ligand by the factor $1+[A]/K_A$; equivalently, at a fixed positive free tracer concentration, the competitor's half-inhibitory free concentration is $\mathrm{IC}_{50}=K_A(1+[L]/K_L)$, the Cheng–Prusoff relation.

**Setting.** A receptor $R$ with one class of identical sites binds either a labelled ligand $L$ or a competitor $A$, never both at once. At equilibrium (ideal activities), with **free** concentrations $[R],[L],[A]\ge0$ and dissociation constants $K_L,K_A>0$,

$$K_L[RL]=[R][L],\qquad K_A[RA]=[R][A],\qquad [R]+[RL]+[RA]=R_T>0.$$

**Statement.**

1. The occupancy by $L$ is

$$\frac{[RL]}{R_T}=\frac{[L]}{[L]+K_L\left(1+[A]/K_A\right)},$$

so at fixed free $[A]$ the $L$ saturation curve is the [single-class isotherm](single-class-binding-isotherm.md) with apparent dissociation constant $K_{L,\mathrm{app}}=K_L(1+[A]/K_A)$: a parallel shift by $\log(1+[A]/K_A)$ on a logarithmic concentration axis.

2. Fix a free tracer concentration $[L]>0$ and let $B([A])=[RL]$. Then $B$ is strictly decreasing in $[A]$, $B([A])=B(0)/2$ holds for exactly one $[A]$, namely

$$[A]=\mathrm{IC}_{50}=K_A\left(1+\frac{[L]}{K_L}\right),\qquad\text{so}\qquad K_i:=K_A=\frac{\mathrm{IC}_{50}}{1+[L]/K_L}.$$

(At $[L]=0$ there is no specific binding and no $\mathrm{IC}_{50}$.)

3. For $[A]>0$, $\ln\!\left(K_{L,\mathrm{app}}/K_L-1\right)=\ln([A]/K_A)$, a line of unit slope against the dimensionless abscissa $\ln([A]/c^\circ)$ for any reference concentration $c^\circ$ (the affinity-ratio or Schild-type plot). A slope different from one is inconsistent with this ideal competitive model; it may motivate testing an allosteric alternative but does not by itself establish one, since heterogeneous sites, non-equilibrium or concentration-accounting errors can also cause it.

Items 1–3 use free concentrations. If the plotted concentrations are totals, they approximate the free values when depletion of both ligands is negligible (exact equality requires zero depletion); otherwise both ligand balances must be solved, and with depletion of the tracer a further correction (the Goldstein–Barrett term described by Hulme and Trevethick, whose formula is rendered as an image in the copy read and is not reproduced here) adds to the Cheng–Prusoff shift.

## Context

Undergraduate to graduate pharmacology and biochemistry. Displacement assays with a labelled tracer are the standard way to rank the affinities of unlabelled compounds, and the Cheng–Prusoff factor converts an observed $\mathrm{IC}_{50}$ into an affinity. No Artzi-specific result depends on this page.

## Depends on

- [Equilibrium occupancy of one class of independent binding sites](single-class-binding-isotherm.md)

## Proof depends on

None.

## Expansion

Proof: substituting $[RL]=[R][L]/K_L$ and $[RA]=[R][A]/K_A$ into the conservation law gives $[R]=R_T/(1+[L]/K_L+[A]/K_A)$, hence item 1. For item 2, $B([A])=R_T[L]/([L]+K_L+K_L[A]/K_A)$ is positive and strictly decreasing when $[L]>0$; the equation $B([A])=B(0)/2$ is linear in $[A]$ and gives $K_L[A]/K_A=[L]+K_L$. Item 3 is the logarithm of $K_{L,\mathrm{app}}/K_L-1=[A]/K_A$, which needs $[A]>0$.

Remaining decomposition before the page can be marked ready: (i) a definition page for the two-ligand competitive mass-action model (mutually exclusive binding at one site class); (ii) a separate page, if wanted, for the total-concentration and tracer-depletion corrections, which requires a text-readable source for the Goldstein–Barrett formula.

## Sources

- E. C. Hulme and M. A. Trevethick, "Ligand binding assays at equilibrium: validation and interpretation", *British Journal of Pharmacology* 161(6) (2010), 1219–1237, [doi.org](https://doi.org/10.1111/j.1476-5381.2009.00604.x); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC3000649/): the Cheng–Prusoff transformation $K_i=\mathrm{IC}_{50}/(1+[L]/K_{dL})$ in the introduction; the competition section stating the ratio $K_{dL\mathrm{app}}/K_{dL}=1+[A]/K_{dA}$, the parallel shifts, the requirement that free concentrations be used, the affinity-ratio plot of $\log(K_{dL\mathrm{app}}/K_{dL}-1)$ against $\log[A]$ with unit slope for competition (Figure 5), and the existence of the Goldstein–Barrett depletion correction.
- O. Arunlakshana and H. O. Schild, "Some quantitative uses of drug antagonists", *British Journal of Pharmacology and Chemotherapy* 14(1) (1959), 48–58, [doi.org](https://doi.org/10.1111/j.1476-5381.1959.tb00928.x); only the abstract was accessible as text ([pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC1481829/)), which states the hypothesis that agonists and antagonists compete for receptors according to the mass law; it is cited for that hypothesis only.
