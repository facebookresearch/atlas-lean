# Pairwise and K-pairwise maximum entropy models of spiking patterns

**Maximum entropy principle.** Let $\sigma = (\sigma_1, \dots, \sigma_N) \in \{0, 1\}^N$ record which of $N$ neurons spike in a time bin, and let $f_1, \dots, f_M$ be functions of $\sigma$ whose empirical means $\langle f_\mu \rangle_{\mathrm{data}}$ are measured. Among all distributions on $\{0,1\}^N$ with $\langle f_\mu \rangle_P = \langle f_\mu \rangle_{\mathrm{data}}$ for all $\mu$, the one of maximal entropy (when the constraints are satisfiable by a distribution of full support) is

$$P(\sigma) = \frac{1}{Z}\, e^{-E(\sigma)}, \qquad E(\sigma) = -\sum_{\mu=1}^{M} g_\mu f_\mu(\sigma), \qquad Z = \sum_{\sigma} e^{-E(\sigma)},$$

with couplings $g_\mu$ fixed by the moment-matching equations; these have a unique solution because the log-partition function $\log Z(g)$ is strictly convex in $g$ (for affinely independent $f_\mu$) and maximum-likelihood fitting of the exponential family is equivalent to matching the moments.

**Pairwise model.** Constraining the firing probabilities $\langle \sigma_i \rangle$ and pairwise moments $\langle \sigma_i \sigma_j \rangle$ gives the Ising-type model

$$P_2(\sigma) = \frac{1}{Z}\exp\Big(\sum_{i} h_i \sigma_i + \frac12 \sum_{i \ne j} J_{ij}\, \sigma_i \sigma_j\Big).$$

**K-pairwise model.** Adding the constraint that the distribution of the population count $K(\sigma) = \sum_i \sigma_i$ match the data, $P(K = k)$ for $k = 0, \dots, N$, adds a global potential:

$$P_{K2}(\sigma) = \frac{1}{Z}\exp\Big(\sum_{i} h_i \sigma_i + \frac12 \sum_{i \ne j} J_{ij}\, \sigma_i \sigma_j + V\big(K(\sigma)\big)\Big),$$

with $V : \{0, \dots, N\} \to \mathbb R$ chosen to reproduce the observed synchrony distribution. This adds only about $N$ parameters to the roughly $N^2/2$ of the pairwise model, and reproduces in particular the probability of the all-silent pattern exactly.

**Effective field.** In both models the conditional spiking probability of one neuron given the others is logistic in an effective field:

$$P(\sigma_i = 1 \mid \sigma_{-i}) = \frac{1}{1 + e^{-h^{\mathrm{eff}}_i}}, \qquad h^{\mathrm{eff}}_i = E(\sigma_{-i}, \sigma_i = 0) - E(\sigma_{-i}, \sigma_i = 1),$$

which for the pairwise model is $h_i + \sum_{j \ne i} J_{ij}\sigma_j$ and for the K-pairwise model additionally contains $V(K_{-i} + 1) - V(K_{-i})$, $K_{-i} = \sum_{j \ne i}\sigma_j$.

## Expansion

The Gibbs form follows from Lagrange multipliers: maximizing $-\sum_\sigma P\log P$ subject to normalization and the moment constraints gives $\log P(\sigma) = \text{const} + \sum_\mu g_\mu f_\mu(\sigma)$. Strict convexity of $\log Z$ follows because its Hessian is the covariance matrix of $(f_\mu)$ under $P$. The effective field formula is the ratio $P(\sigma_i = 1, \sigma_{-i}) / P(\sigma_i = 0, \sigma_{-i}) = e^{h^{\mathrm{eff}}_i}$, in which $Z$ cancels. For recordings of up to 120 salamander retinal ganglion cells responding to natural movies, pairwise models captured most of the structure for small groups but, for 40 or more neurons, misestimated the probability of many simultaneous spikes; the K-pairwise model fixed this and predicted held-out statistics such as triplet correlations and the distribution of pattern energies, and the effective-field relation was confirmed on held-out data.

## Sources

- G. Tkačik, O. Marre, D. Amodei, E. Schneidman, W. Bialek, M. J. Berry II, "Searching for collective behavior in a large network of sensory neurons", PLoS Computational Biology (2014), Introduction and Results, Eqs. (1)–(4) (maximum entropy construction), Eq. (19) (pairwise model), Eq. (20) (K-pairwise model) and Eqs. (25)–(26) (effective field), <https://doi.org/10.1371/journal.pcbi.1003408> (PMC3879139).
