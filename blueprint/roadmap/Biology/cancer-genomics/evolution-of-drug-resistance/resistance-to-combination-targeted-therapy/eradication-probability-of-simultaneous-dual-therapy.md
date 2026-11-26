# Eradication probability of simultaneous dual therapy

In the [multitype birth–death model of combination-therapy resistance](multitype-birth-death-model-of-combination-therapy-resistance.md), with $s = 1 - d/b \in (0,1)$ and $s' = 1 - d'/b' < 0$, the probability that simultaneous two-drug therapy started at lesion size $M$ eradicates the lesion is

$$p_{\mathrm{erad}} = p_{1\uparrow}\, p_{1\downarrow}\, p_{2\uparrow}\, p_{2\downarrow},$$

the product of the probabilities that no surviving fully resistant lineage arises by one mutational step before ($\uparrow$) or during ($\downarrow$) treatment, and by two steps before or during treatment. In the large-$M$, small-$u$ regime,

$$p_{1\uparrow} = \exp(-M u\, n_{12}), \qquad p_{1\downarrow} = \exp\!\Bigl(\frac{M u\, n_{12}\, s}{s'}\Bigr), \qquad p_{2\downarrow} = \exp\!\Bigl(-\frac{M u^2\,\bigl(2 n_1 n_2 + n_{12}(n_1 + n_2)\bigr)\, s}{s'^2}\Bigr),$$

$$p_{2\uparrow} = \exp\!\Bigl[\frac{M u^2 (s' - s)}{s s'}\Bigl(n_1 (n_2 + n_{12}) \log\Bigl(\frac{1}{sM} + \frac{u (n_2 + n_{12})(s' - s)}{s s'}\Bigr) + n_2 (n_1 + n_{12}) \log\Bigl(\frac{1}{sM} + \frac{u (n_1 + n_{12})(s' - s)}{s s'}\Bigr)\Bigr)\Bigr].$$

All four exponents are nonpositive; each vanishes when no mutational path of its kind exists (the one-step exponents when $n_{12} = 0$). The four failure routes are treated as independent, which gives the product form.

## Depends on

- [Multitype birth–death model of resistance to combination therapy](multitype-birth-death-model-of-combination-therapy-resistance.md)

## Expansion

During treatment the sensitive population declines from $M$ at net rate $b' - d' < 0$, so the expected total number of sensitive divisions is about $M b'/(d' - b') = -M/s'$. Each division yields a type-$11$ cell with probability $u n_{12}$, and its lineage survives with probability $s$; the number of surviving one-step lineages is approximately Poisson with mean $-M u n_{12} s / s'$, giving $p_{1\downarrow}$. Two-step lineages during treatment need an intermediate single-resistant mutant (growing at the resistant rates for one drug but declining under the other) followed by a second mutation, giving the $u^2/s'^2$ scaling of $p_{2\downarrow}$. The source verifies the formula against branching-process simulations. Its applications: monotherapy fails for detectable lesions when about 50 resistance mutations exist; with even one cross-resistance mutation dual therapy rarely cures patients with large disease burden, whereas without cross-resistance most patients with small burden are cured; sequential therapy with the same two drugs fails where simultaneous therapy succeeds, because resistance to the second drug accumulates during treatment with the first. Proofs are in Supplementary file 1, Section 5, of the source.

## Sources

- I. Bozic, J. G. Reiter, B. Allen, T. Antal, K. Chatterjee, P. Shah, et al., "Evolutionary dynamics of cancer in response to targeted combination therapy", *eLife* 2 (2013), e00747, Equation (1) and the formulas for $p_{1\uparrow}, p_{1\downarrow}, p_{2\uparrow}, p_{2\downarrow}$ that follow it, <https://doi.org/10.7554/eLife.00747> (PMC3691570).
