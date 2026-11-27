# Drug-concentration-dependent growth-rate landscape

**Setting.** A combinatorially complete set of alleles at $L$ sites (here the $2^4 = 16$ alleles of dihydrofolate reductase at four resistance-associated sites) is assayed for its drugless growth rate and its half-maximal inhibitory concentration in a drug.

**Statement** (Ogbunugafor, Wylie, Diakite, Weinreich and Hartl 2016, eqs. (1)–(2)). The growth rate of an allele at drug concentration $x$ (on a logarithmic concentration scale) is taken to be the decreasing logistic function of two measured parameters,

$$g(x) = \frac{g_{\mathrm{drugless}}}{1 + e^{(x - \mathrm{IC}_{50})/c}},$$

where $g_{\mathrm{drugless}}$ is the growth rate without drug, $\mathrm{IC}_{50}$ the concentration halving the growth rate, and $c > 0$ a fitted shape constant; this assigns to every drug concentration a fitness landscape on the $2^L$ alleles. The effect of adding a single mutation $\varepsilon$ to a background allele $j$ is

$$\Delta W_\varepsilon = W_{j_\varepsilon} - W_j,$$

evaluated on each of the $2^{L-1}$ backgrounds, and the degree of epistasis for that mutation in that environment is measured by the dispersion (standard deviation) of $\Delta W_\varepsilon$ over backgrounds. Because the landscape is indexed by the environment, the rank order of allele fitnesses, and hence which mutational trajectories are selectively accessible, is itself a function of drug concentration.

## Depends on

- [Fitness landscapes as mathematical objects](../../population-genetics/selection-migration-and-transmission/fitness-landscapes/fitness-landscapes-as-explicit-mathematical-obje.md)
- [Accessible mutational paths in the House-of-Cards landscape](../../population-genetics/selection-migration-and-transmission/fitness-landscapes/accessible-adaptive-paths.md)

## Expansion

Two alleles' growth curves cross whenever one has the larger drugless rate and the other the larger $\mathrm{IC}_{50}$: at $x \ll \mathrm{IC}_{50}$ the curve is flat near $g_{\mathrm{drugless}}$, at $x \gg \mathrm{IC}_{50}$ it decays, so the ranking at low concentration is by $g_{\mathrm{drugless}}$ and at high concentration by $\mathrm{IC}_{50}$. Every such crossing can change the set of accessible paths, so resistance measured by $\mathrm{IC}_{50}$ alone does not determine which allele wins: the most resistant allele is favoured only at extreme concentrations. The dispersion measure of epistasis records the same dependence one level down: a mutation whose effect is nearly constant across backgrounds in one environment can have a widely varying effect in another, and absolute effects must be compared with the ancestral growth rate at that concentration, since a large absolute effect in an environment where every allele grows well changes the dynamics little.

## Sources

- C. B. Ogbunugafor, C. S. Wylie, I. Diakite, D. M. Weinreich and D. L. Hartl, "Adaptive landscape by environment interactions dictate evolutionary dynamics in models of drug resistance", PLoS Computational Biology 12 (2016), e1004710, Methods ("From empirical data to estimated growth rate", "Effect of mutation as a function of the environment", "Quantifying epistasis"), eqs. (1)–(2), and Results (Table 1), <https://doi.org/10.1371/journal.pcbi.1004710>, PMCID PMC4726534.
