# Multi-rate Poisson tree process

**Setting.** $T = (V, E)$ is a rooted binary phylogenetic tree with branch lengths $\ell(x) > 0$ in expected substitutions per site. A *delimitation* is a connected subtree $G = (V_s, E_s)$ of $T$ containing the root that is itself a binary tree (every node of $G$ has both or neither of its child branches in $E_s$) (the speciation process); the remaining branches $E_c = E \setminus E_s$ form maximal subtrees $T_1 = (V_1, E_1), \dots, T_k = (V_k, E_k)$ with disjoint vertex sets and $\bigsqcup_i E_i = E_c$, one per delimited species, rooted at the *coalescent roots*.

**Single-rate PTP.** Branch lengths are i.i.d. exponential with one rate $\lambda_s$ on $E_s$ and one rate $\lambda_c$ on $E_c$:

$$L = \prod_{x \in E_s} \hat\lambda_s e^{-\hat\lambda_s \ell(x)} \prod_{x \in E_c} \hat\lambda_c e^{-\hat\lambda_c \ell(x)} \qquad \text{(Eq. 1)}.$$

**Multi-rate PTP (mPTP).** Each species has its own coalescent rate:

$$L = \prod_{i=1}^{k} \prod_{x \in E_i} \hat\lambda_i e^{-\hat\lambda_i \ell(x)} \times \prod_{x \in E_s} \hat\lambda_s e^{-\hat\lambda_s \ell(x)} \qquad \text{(Eq. 2)},$$

with maximum-likelihood rates $\hat\lambda_i = \big(\frac{1}{|E_i|}\sum_{x \in E_i}\ell(x)\big)^{-1}$ and likewise $\hat\lambda_s$.

**Profile log-likelihood.** Substituting the rate estimates, for each block $B \in \{E_s, E_1, \dots, E_k\}$ with $n_B = |B|$ and $\Sigma_B = \sum_{x \in B}\ell(x)$,

$$\log L = \sum_{B} n_B\big(\log n_B - \log \Sigma_B - 1\big).$$

**Model selection and support.** Among candidate delimitations the one minimizing the small-sample Akaike criterion $\mathrm{AIC}_c$ (one rate parameter per block) is chosen, which penalizes over-splitting; the null model ($i = 0$ speciation branches) is a single exponential. Support for a node is the sum of Akaike weights of delimitations placing it in the speciation process, approximated by MCMC with split/merge moves of coalescent roots and acceptance ratio $\alpha = \frac{L_c'}{L_c}\cdot\frac{g(\theta' \to \theta)}{g(\theta \to \theta')}$, where $L_c$ is the $\mathrm{AIC}_c$-corrected likelihood.

## Expansion

Within a species, branching events are frequent relative to substitutions; between species they are rare, so the number of substitutions between successive branchings is modeled as exponential with a species- or process-specific rate. For a block of $n$ exponential lengths the MLE is $\hat\lambda = n/\Sigma$ and the maximized log-likelihood is $n\log\hat\lambda - \hat\lambda\Sigma = n(\log n - \log \Sigma - 1)$, which gives the profile formula. Because the optimization over delimitations has no known polynomial algorithm, the source uses a greedy bottom-up dynamic program: each node stores, for every possible number $i$ of speciation branches in its subtree, the best score, combining child entries $j, k$ with $i = j + k + 2$; its average running time is $O(n^2)$ in the number of nodes. Allowing distinct $\lambda_i$ accommodates species that differ in effective population size, structure or sampling depth.

## Sources

- P. Kapli, S. Lutteropp, J. Zhang, K. Kobert, P. Pavlidis, A. Stamatakis, T. Flouri, "Multi-rate Poisson tree processes for single-locus species delimitation under maximum likelihood and Markov chain Monte Carlo", Bioinformatics 33(11) (2017) 1630–1638, Sections 2.1–2.2, Eqs. 1–2, <https://doi.org/10.1093/bioinformatics/btx025> (PMC5447239).
- J. Zhang, P. Kapli, P. Pavlidis, A. Stamatakis, "A general species delimitation method with applications to phylogenetic placements", Bioinformatics 29 (2013) 2869–2876.
