# Pseudo-first-order approach to binding equilibrium

When the free ligand concentration is held constant, the complex of $R+L\rightleftharpoons RL$ relaxes exponentially to equilibrium with observed rate $k_{\mathrm{obs}}=k_{\mathrm{on}}[L]+k_{\mathrm{off}}$; equilibration is slowest at the lowest ligand concentrations, where $k_{\mathrm{obs}}\to k_{\mathrm{off}}$.

**Setting.** Mass-action kinetics for one class of sites with association rate constant $k_{\mathrm{on}}>0$ (M$^{-1}$s$^{-1}$) and dissociation rate constant $k_{\mathrm{off}}>0$ (s$^{-1}$), total receptor $R_T>0$:

$$\frac{d[RL]}{dt}=k_{\mathrm{on}}[R][L]-k_{\mathrm{off}}[RL],\qquad [R]=R_T-[RL],\qquad t\ge0.$$

Premise (pseudo-first-order clamping): the free ligand concentration is exactly constant, $[L]=c\ge0$. In practice large ligand excess or buffering only approximates this premise.

**Statement.** With $K_d=k_{\mathrm{off}}/k_{\mathrm{on}}$ and initial value $[RL]\,(0)=y_0$ with $0\le y_0\le R_T$, the unique solution is

$$[RL]\,(t)=y_\infty+(y_0-y_\infty)\,e^{-k_{\mathrm{obs}}t},\qquad k_{\mathrm{obs}}=k_{\mathrm{on}}c+k_{\mathrm{off}},\qquad y_\infty=\frac{R_T\,c}{c+K_d},$$

and it stays in $[0,R_T]$. The equilibrium value is the [single-class isotherm](single-class-binding-isotherm.md) with $K_d=k_{\mathrm{off}}/k_{\mathrm{on}}$; the deviation from equilibrium halves every $\ln 2/k_{\mathrm{obs}}$; and $k_{\mathrm{obs}}\ge k_{\mathrm{off}}$ with equality at $c=0$, so $k_{\mathrm{off}}$ bounds the relaxation rate from below at every clamped ligand concentration. After five half-times the remaining deviation is exactly $2^{-5}=1/32$ of the initial one (96.875% of the way to equilibrium); if $y_0=y_\infty$ no waiting is needed.

## Context

Undergraduate to graduate. The cited sources use this to choose incubation times: when approaching equilibrium from a displaced state, incubating for several half-times at the lowest concentration used is a practical guideline for a chosen tolerance, not a logical requirement, and the single-step rate law need not describe multistep binding. No Artzi-specific result is derived.

## Depends on

- [Equilibrium occupancy of one class of independent binding sites](single-class-binding-isotherm.md)

## Proof depends on

- [Integrated first-order rate law](../../../../Chemistry/chemical-kinetics/rate-laws/first-order-sol.md)

## Expansion

Proof: with $c$ constant the equation is linear, $\dot y=k_{\mathrm{on}}cR_T-(k_{\mathrm{on}}c+k_{\mathrm{off}})y$. Its unique solution comes from applying the first-order decay law to $y-y_\infty$, where $y_\infty=k_{\mathrm{on}}cR_T/(k_{\mathrm{on}}c+k_{\mathrm{off}})$ is the zero of the right-hand side; dividing by $k_{\mathrm{on}}$ gives the stated form. The solution is a convex combination of $y_0$ and $y_\infty$, both in $[0,R_T]$.

Remaining decomposition before the page can be marked ready: (i) a uniqueness statement for linear first-order ODEs with constant coefficients (the first-order rate-law page covers the homogeneous case $\dot u=-ku$; the shift $u=y-y_\infty$ must be stated); (ii) the model premise that $[L]$ is exactly constant should be a hypothesis of the definition, with depletion handled on a separate page (Hulme and Trevethick give the integrated rate equation under depletion, their Eq. 4, rendered as an image and not used here).

## Sources

- I. Jarmoskaite et al., "How to measure and evaluate binding affinities", *eLife* 9 (2020), e57264, [doi.org](https://doi.org/10.7554/eLife.57264); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC7452723/), section "Vary the incubation time", Eqs. 1–2 ($k_{\mathrm{equil}}=k_{\mathrm{on}}[P]+k_{\mathrm{off}}$ and its limit $k_{\mathrm{off}}$ at low concentration; fraction approached $1-e^{-k_{\mathrm{equil}}t}$; equilibration time taken as five half-lives).
- E. C. Hulme and M. A. Trevethick, "Ligand binding assays at equilibrium: validation and interpretation", *British Journal of Pharmacology* 161(6) (2010), 1219–1237, [doi.org](https://doi.org/10.1111/j.1476-5381.2009.00604.x); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC3000649/), section "Time-course of binding and dissociation" (rate equation for the complex and the association time course, Eq. 2, rendered as an image; text checked).
