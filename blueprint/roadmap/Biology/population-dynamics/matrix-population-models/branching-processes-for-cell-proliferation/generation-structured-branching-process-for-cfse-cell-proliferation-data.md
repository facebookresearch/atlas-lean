# Generation-structured branching process for CFSE cell proliferation data

**Model.** A cell population starts from $N_0$ live cells of generation 1. A live cell of generation
$g$ (one that has divided $g - 1$ times) completes its lifespan and then either divides into two live
cells of generation $g + 1$, with probability $p_g$, or dies, with probability $1 - p_g$, becoming a
dead cell of generation $g$; a dead cell of generation $g$ disintegrates after a further time with
distribution function $H_g$. The lifespan of a live cell depends on its fate: its time to division
has distribution function $F_g$ and its time to death $G_g$, so the lifespan has the mixture
distribution $p_g F_g + (1 - p_g) G_g$. With $F_g = G_g$ this is a multitype Bellman–Harris process.
Cells evolve independently.

**Expected generation sizes.** Let $Z_{g,1}(t)$ and $Z_{g,0}(t)$ be the numbers of live and dead cells
of generation $g$ at time $t$, $m_{g,s}(t)$ their expectations for one initiator cell, and
$\mathcal{F}_{g} = F_1 * F_2 * \cdots * F_{g}$ the convolution of the first $g$ division-time
distributions ($\mathcal{F}_0 = 1$, the unit step at $0$). Then

$$m_{g,1}(t) = 2^{g-1}\Bigl(\prod_{i=1}^{g-1} p_i\Bigr)\Bigl[\mathcal{F}_{g-1}(t)
 - \bigl(\mathcal{F}_{g-1} * (p_g F_g + (1 - p_g) G_g)\bigr)(t)\Bigr],$$

$$m_{g,0}(t) = 2^{g-1}\Bigl(\prod_{i=1}^{g-1} p_i\Bigr)(1 - p_g)\Bigl[(\mathcal{F}_{g-1} * G_g)(t)
 - (\mathcal{F}_{g-1} * G_g * H_g)(t)\Bigr].$$

These expressions remain valid without the independence assumption provided the convolutions are
replaced by distribution functions of the corresponding sums of possibly dependent lifespans along a
lineage; in particular, dependence between cells that are not in direct line of descent (sisters,
cousins, aunts) does not change the expected generation sizes.

**Competing-risk special case.** If division and death are decided by independent latent times
$\lambda_{g,1} \sim \mathrm{Exp}(\theta_{g,1})$ and $\lambda_{g,0} \sim \mathrm{Exp}(\theta_{g,0})$, the
smaller one determining both fate and lifespan, then $p_g = \theta_{g,1}/(\theta_{g,0} + \theta_{g,1})$
and $F_g(t) = G_g(t) = 1 - e^{-(\theta_{g,0} + \theta_{g,1}) t}$, so division and death times cannot
differ in distribution.

## Expansion

By linearity of expectation, $m_{g,1}(t)$ sums over the $2^{g-1}$ potential generation-$g$
descendants of one initiator: each exists only if all $g - 1$ ancestral cells divided (probability
$\prod_{i<g} p_i$), is born at the sum of $g - 1$ division times (distribution $\mathcal{F}_{g-1}$), and
is alive at $t$ if born by $t$ but has not yet completed its own lifespan. Dead cells are counted
between death and disintegration. Only the marginal law of each lineage enters, which is why
dependence across lineages is irrelevant for the mean. With $N_0$ large, the proportions
$Z_{g,s}(t)/\sum Z$ are approximated by $m_{g,s}(t)/\sum m$, and the CFSE fluorescence of the
population is a mixture over generations whose mean log-intensity drops by $\log 2$ per division.
Allowing $F_g \neq G_g$ while letting $p_g$ vary freely in $[0, 1]$ is what the competing-risk
(cyton-type) formulation cannot do.

## Sources

- O. Hyrien, R. Chen, M. S. Zand, "An age-dependent branching process model for the analysis of
  CFSE-labeling experiments", Biology Direct 5 (2010) 41, model description, Eqs. (1)-(6) and
  Proposition 1, <https://doi.org/10.1186/1745-6150-5-41> (PMC2914727).
