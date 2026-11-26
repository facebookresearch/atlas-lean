# MSMC: first-coalescence hidden Markov model

**Model.** Let $M \ge 2$ phased haplotypes be sampled from one panmictic population whose scaled coalescence rate (inverse relative population size) is a function $\lambda(t) > 0$ of scaled time $t$ before the present, and let $\rho$ be the scaled recombination rate. At each genomic position, the multiple sequentially Markovian coalescent (MSMC) hidden state is the triple $(t, i, j)$: the time $t$ of the **first** coalescence among the $M$ lineages and the unordered pair $\{i,j\}$ of haplotypes that coalesce first. Along the sequence the state changes according to the SMC′ approximation (a recombination on the local genealogy may or may not alter the first coalescence), and emissions depend on the state and on a locally estimated singleton branch length.

**Proposition (law of the hidden state).** Under the coalescent, each of the $\binom M2$ pairs coalesces at rate $\lambda(t)$ until the first coalescence, so

$$\Pr(T_{\mathrm{first}} > t) = \exp\!\Big(-\tbinom M2\int_0^t\lambda(v)\,dv\Big),\qquad f_{T_{\mathrm{first}}}(t) = \tbinom M2\lambda(t)\exp\!\Big(-\tbinom M2\int_0^t\lambda(v)\,dv\Big),$$

and the first-coalescing pair is uniform over the $\binom M2$ pairs and independent of $T_{\mathrm{first}}$. At constant rate $\lambda$ the expected first-coalescence time is $1/(\binom M2\lambda)$, so the time window informed by the data moves toward the present roughly as $M^{-2}$.

**Inference.** With $\lambda$ piecewise constant on time segments ($\lambda_i$ on segment $i$, boundaries scaled by $\binom M2$), the parameters are fitted by Baum–Welch expectation-maximization, and relative population sizes are read off as $N_i/N_0 = 1/\lambda_i$, where $N_0 = \theta/(4\mu)$ is fixed by Watterson's estimate of the scaled mutation rate $\theta$ and a per-generation mutation rate $\mu$. For $M = 2$ the model reduces to a pairwise SMC′ variant of PSMC (called PSMC′). In practice two, four and eight haplotypes resolve history over roughly $40$ kya–$3$ Mya, $8$–$300$ kya and $2$–$50$ kya.

## Depends on

- [Pairwise sequentially Markov coalescents SMC and SMC′](../../two-locus-coalescent/sequentially-markov-coalescent-smc-smc-pairwise.md)
- [Classic skyline estimate of population size](../../skyline-plot-estimates-of-population-size/skyline-estimate.md)

## Expansion

The minimum of $\binom M2$ independent clocks with common hazard $\lambda(t)$ has hazard $\binom M2\lambda(t)$, which gives the survival function; by symmetry the identity of the clock that rings first is uniform and independent of when it rings. Restricting the hidden state to the first coalescence, instead of the whole local tree, keeps the state space at $\binom M2$ pairs times the number of time segments, which is what makes multiple haplotypes tractable. The cost is two approximations: the SMC′ transition kernel for the first-coalescence process, and summarizing the rest of the tree by the singleton branch length in the emission model.

## Sources

- S. Schiffels and R. Durbin, "Inferring human population size and separation history from multiple genome sequences", Nature Genetics 46 (2014), Online Methods ("Transition Rate", "Emission Rate", "Parameter Inference") and Results, <https://doi.org/10.1038/ng.3015> (PMC4116295).
