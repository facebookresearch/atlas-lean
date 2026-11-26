# Marginal visible transition density under the SMC$'$

Let local genealogies of $n$ sequences evolve along a chromosome as the embedded chain of the sequentially Markov coalescent SMC$'$ with effective size trajectory $N(t)$. At a recombination breakpoint the current genealogy $g_{i-1}$ is modified by choosing a pruning location $p_i = (u_i, w_i)$ uniformly along the tree — uniformly over its total length $\ell_{i-1}$ — detaching the branch above $u_i$ on lineage $w_i$ and regrafting it at a new coalescence time $t^i_{\mathrm{new}}$ on some lineage $c_i$. Writing $A^{i-1}(t)$ for the number of ancestral lineages of $g_{i-1}$ at time $t$, the joint density of a pruning location and a regrafting is

$$\Pr\bigl[p_i = (u_i,w_i),\, t^i_{\mathrm{new}},\, c_i \mid g_{i-1}, N(t)\bigr] = \frac{1}{\ell_{i-1}} \cdot \frac{1}{N(t^i_{\mathrm{new}})} \exp\left\{- \int_{u_i}^{t^i_{\mathrm{new}}} \frac{A^{i-1}(t)}{N(t)}\, dt \right\} .$$

A transition is **visible** when the resulting genealogy $g_i$ differs from $g_{i-1}$. Since the pruning location is not observed, let $I^{i-1}(t) \in \{0,1,2\}$ be the number of branches of $g_{i-1}$ at time $t$ on which a pruning would have produced exactly the observed transition to $g_i$. Averaging over pruning locations gives the marginal visible transition density

$$\Pr[G_i = g_i \mid g_{i-1}, N(t)] = \frac{1}{\ell_{i-1}} \int_0^\infty I^{i-1}(u) \, \frac{1}{N(t^i_{\mathrm{new}})} \exp\left\{- \int_{u}^{t^i_{\mathrm{new}}} \frac{A^{i-1}(t)}{N(t)} \, dt\right\} du .$$

In addition, the distance $S_i$ to the next breakpoint depends on the current genealogy only through its total length: $f(s_i \mid g_{i-1}, \rho) = \rho\,\ell_{i-1} e^{-\rho \ell_{i-1} s_i}$, with $\rho$ the per-site recombination rate.

## Depends on

- [Pairwise sequentially Markov coalescents SMC and SMC′](../sequentially-markov-coalescent-smc-smc-pairwise.md)
- [The time-changed coalescent as the limit of a Wright–Fisher model of varying size](../../site-frequency-spectrum-under-variable-populatio/derivation-of-the-time-changed-coalescent-from-a.md)

## Expansion

The step function $I^{i-1}$ is what makes the pruning location only partially identifiable: comparing $g_{i-1}$ with $g_i$ usually pins the pruned lineage down to a single branch over an interval of times, in which case $I^{i-1}(t) = 1$ below the deleted coalescence time $t^i_{\mathrm{del}}$ and $0$ above it, but when the children of the node at $t_{\mathrm{del}}$ coincide with the children of the node at $t_{\mathrm{new}}$ two different prunings produce the same visible transition and $I^{i-1}(t) = 2$. The first local genealogy $g_0$ contributes the standard coalescent density $\prod_{j=2}^{n} N(t^0_j)^{-1} \exp\{-\int_{t^0_{j+1}}^{t^0_j} A^0(t)(A^0(t)-1)/(2N(t))\,dt\}$. These densities, together with the invisible-transition probabilities, are the complete set of factors needed for likelihood-based inference of $N(t)$ from a sequence of local genealogies.

## Sources

- J. A. Palacios, J. Wakeley, S. Ramachandran, "Bayesian nonparametric inference of population size changes from sequential genealogies", *Genetics* 201 (2015), 281–304, <https://doi.org/10.1534/genetics.115.177980> (PMC4566269). Methods: SMC$'$ calculations, Equations (1)–(8).
