# FLARE hidden Markov model for local ancestry

Let a phased admixed haplotype be modeled against $J$ phased reference panels, panel $j$ containing $n_j$ haplotypes, with $A$ contributing ancestries. The FLARE model is a hidden Markov model whose hidden state at marker $m$ is $S_m = (i, h)$: the ancestry $i \in \{1, \dots, A\}$ of the target at that position and the reference haplotype $h$ it copies. Its parameters are global ancestry proportions $\mu_i > 0$ with $\sum_i \mu_i = 1$, panel-copying probabilities $p_{ij} \ge 0$ with $\sum_j p_{ij} = 1$, an admixture time $T > 0$ (generations), ancestry-specific switch rates $\rho_i > 0$, and mismatch rates $\theta_{ij} \in [0, 1)$.

- **Prior.** For $h$ in panel $j$ put $q_{ih} = p_{ij}/n_j$. The initial (prior) state probabilities are $\pi(i, h) = \mu_i q_{ih}$.
- **Ancestry changes.** For consecutive markers $m-1, m$ separated by $d_m$ Morgans, an ancestry-changing crossover occurs with probability $1 - e^{-d_m T}$, after which a new ancestry is drawn from $\mu$; a transition to a different ancestry $i' \ne i$ therefore has probability $\mu_{i'}(1 - e^{-d_m T})$, and the new donor $h'$ is drawn from $q_{i'\cdot}$.
- **Donor changes within an ancestry.** Without an ancestry change, a new donor is drawn from $q_{i\cdot}$ with probability $1 - e^{-d_m\rho_i}$.
- **Emission.** If $I_m(h) = 1$ when haplotype $h$ carries the observed target allele at $m$ and $0$ otherwise, then for $h$ in panel $j$, $e_m(i, h) = 1 - \theta_{ij}$ if $I_m(h) = 1$ and $e_m(i,h) = \theta_{ij}$ otherwise (biallelic markers).

Under the reading that an ancestry crossover redrawing the same ancestry also redraws the donor, the transition kernel is, with $a = e^{-d_mT}$ and $b_i = e^{-d_m\rho_i}$,

$$P\big((i,h)\to(i',h')\big) = \begin{cases} (1-a)\,\mu_{i'}\,q_{i'h'}, & i' \ne i,\\ a\,b_i\,\mathbf 1[h'=h] + \big(a(1-b_i) + (1-a)\mu_i\big)\,q_{ih'}, & i' = i,\end{cases}$$

whose rows sum to one. Local ancestry is called as the ancestry with the largest posterior probability $\Pr(S_m \in \{i\}\times\text{panels} \mid \text{data})$, computed by forward–backward recursions.

## Depends on

- [The Li–Stephens copying model](hmm.md)
- [Stationary Poisson-relabeling model of local ancestry](../admixture-linkage-disequilibrium/poisson-switch-markov-model-of-local-ancestry-al.md)

## Expansion

Ancestry tracts arise from crossovers in the $T$ generations since admixture, so the ancestry process alone is the Poisson-relabeling chain with rate $T$ per Morgan; within a tract, crossovers before admixture make the copied donor change at rate $\rho_i$, as in the Li–Stephens model. Row sums: $ab_i + \big(a(1-b_i) + (1-a)\mu_i\big) + (1-a)(1-\mu_i) = 1$ using $\sum_{h} q_{ih} = \sum_j p_{ij} = 1$. The paper's exact kernel is given in its supplementary Method S1; FLARE estimates $p_{ij}$ and $\rho_i$ from the reference panels and updates $\mu$ and $T$ by EM.

## Sources

- S. R. Browning, R. K. Waples, B. L. Browning, "Fast, accurate local ancestry inference with FLARE", American Journal of Human Genetics 110 (2023), 326–335, <https://doi.org/10.1016/j.ajhg.2022.12.010> (PMC9943733). Subjects and methods, "Hidden Markov model".
