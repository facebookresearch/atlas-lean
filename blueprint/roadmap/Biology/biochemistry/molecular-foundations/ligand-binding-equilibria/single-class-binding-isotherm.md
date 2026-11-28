# Equilibrium occupancy of one class of independent binding sites

For one-step binding $R+L\rightleftharpoons RL$, the equilibrium fraction of receptor sites occupied is the hyperbolic (Langmuir) function $[L]/(K_d+[L])$ of the free ligand concentration, and it equals one half exactly when the free ligand concentration equals the dissociation constant $K_d$.

**Setting.** A receptor $R$ (or any macromolecule with one class of identical, independent sites, counted per site) binds a ligand $L$ in one step. At equilibrium the free receptor, free ligand and complex concentrations $[R],[L],[RL]$ (in M, ideal activities) satisfy the mass-action relation and the receptor conservation law

$$K_d\,[RL]=[R]\,[L],\qquad [R]+[RL]=[R_T],$$

with dissociation constant $K_d>0$ (equivalently association constant $K=1/K_d$, in M$^{-1}$), total receptor $[R_T]>0$ and free ligand $[L]\ge 0$.

**Statement.** The fractional occupancy is

$$\theta=\frac{[RL]}{[R_T]}=\frac{[L]}{K_d+[L]}=\frac{K[L]}{1+K[L]}.$$

It is $0$ at $[L]=0$, strictly increasing in $[L]$, tends to $1$ as $[L]\to\infty$, and $\theta=1/2$ if and only if $[L]=K_d$. In the notation of the [Hill response function](../../../systems-biology/goldbeter-koshland-ultrasensitivity/hill.md) it is $h([L])$ with coefficient $n=1$ and half-saturation constant $K_d$. The statement concerns occupancy; a measured response need not be proportional to occupancy.

Here $[L]$ is the **free** ligand concentration. Substituting the total ligand concentration for it is justified when binding depletes only a negligible fraction of the ligand (then the relative error in the free concentration is uniformly small); the exact relation with totals is on [exact binding under ligand depletion](exact-binding-under-ligand-depletion.md).

## Context

Undergraduate biochemistry. This hyperbolic isotherm is the reference curve against which cooperativity, competition and depletion are measured, and the starting point of occupancy-based pharmacology. The Artzi laboratory studies how delivery regimen and administration mode affect the pharmacokinetics and pharmacodynamics of locally delivered therapies (Wyss Institute profile); occupancy of a target by a delivered ligand is the most basic quantity in that analysis. No specific Artzi result depends on this page.

## Depends on

- [Hill response function](../../../systems-biology/goldbeter-koshland-ultrasensitivity/hill.md)

## Proof depends on

None.

## Expansion

Proof: substitute $[RL]=[R][L]/K_d$ into the conservation law to get $[R]\,(1+[L]/K_d)=[R_T]$, hence $[RL]/[R_T]=([L]/K_d)/(1+[L]/K_d)$. Monotonicity and the limits follow from $\theta=1-K_d/(K_d+[L])$, and $\theta=1/2$ is equivalent to $2[L]=K_d+[L]$.

Remaining decomposition before the page can be marked ready: (i) a definition page for ideal one-step mass-action equilibrium with concentration-valued $K_d$ (the statement's model), which no page on main currently provides in this form; (ii) the identification with the Hill page at $n=1$ needs that page's real-power convention $x^1=x$ for $x\ge0$, which should be cited as a separate lemma or stated inline.

## Sources

- E. C. Hulme and M. A. Trevethick, "Ligand binding assays at equilibrium: validation and interpretation", *British Journal of Pharmacology* 161(6) (2010), 1219–1237, [doi.org](https://doi.org/10.1111/j.1476-5381.2009.00604.x); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC3000649/), section "Equilibrium binding" (the mass-action derivation and Eqs. 1a–1b, the Langmuir isotherm; the formulas are rendered as images, and the text states the derivation from $[RL]=K[R][L]$ and receptor conservation).
- I. Jarmoskaite et al., "How to measure and evaluate binding affinities", *eLife* 9 (2020), e57264, [doi.org](https://doi.org/10.7554/eLife.57264); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC7452723/), section "Avoid the titration regime", Eqs. 4a and 4b (fraction bound $=[P]_{\mathrm{free}}/([P]_{\mathrm{free}}+K_D)$ and its total-concentration approximation; the roles of the two partners are swapped relative to this page).
- Wyss Institute faculty profile of Natalie Artzi, [wyss.harvard.edu](https://wyss.harvard.edu/team/core-faculty/natalie-artzi-ph-d/) (context sentence only).
