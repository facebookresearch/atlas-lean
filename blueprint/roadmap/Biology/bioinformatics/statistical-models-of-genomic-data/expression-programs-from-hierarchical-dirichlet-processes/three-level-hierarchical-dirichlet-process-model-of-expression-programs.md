# Three-level hierarchical Dirichlet process model of expression programs

Let a compendium consist of tissue samples $d = 1, \dots, D$, each a bag of expression observations over genes (and, for time series, over qualitative temporal patterns). A **hierarchical Dirichlet process** (HDP) model of expression programs puts a Dirichlet process at each of three levels:

$$G_0 \sim \mathrm{DP}(\gamma, H), \qquad G_g \mid G_0 \sim \mathrm{DP}(\alpha_0, G_0)\ (g = 1,\dots), \qquad G_d \mid G_{g(d)} \sim \mathrm{DP}(\alpha_1, G_{g(d)}),$$

where $H$ is a base measure over program parameters (a distribution over genes, with usage modifiers describing temporal behaviour), $G_0$ is the corpus-level mixture of **expression programs**, $G_g$ the mixture used by **tissue group** $g$, and $G_d$ the mixture used by sample $d$; each observation in sample $d$ draws a program from $G_d$ and then a gene from that program. Because a Dirichlet process draw is almost surely discrete, $G_0$ has countably many atoms and every $G_g$ and $G_d$ re-use exactly those atoms: programs are shared across the whole compendium, more strongly within a group, and a gene may belong to several programs, so programs overlap. The assignment $g(d)$ of samples to groups is itself unobserved and given a Dirichlet process prior, so the numbers of programs and of groups are random and inferred with the data instead of being fixed in advance; the concentration parameters $\gamma, \alpha_0, \alpha_1$ control how strongly atoms are reused and act as a complexity penalty.

## Depends on

- [Dirichlet process](../../../../Probability/bayesian-statistics/dirichlet-process/dirichlet-process.md)

## Remarks

In a plain topic model each document has its own Dirichlet mixture over a fixed number of topics; the hierarchical Dirichlet process replaces that by a random base measure shared across documents, which is what lets the number of components grow with the data and makes components shared rather than document-specific. The middle level encodes the biological assumption that similar tissues use the same programs in the same way. The standard HDP requires the grouping of items to be given; the GeneProgram model of Gerber et al. infers it, so tissue groups and gene programs are learned jointly, and uncertainty in the number of groups propagates into downstream summaries such as the generality score. Applied to 62 short time-series data sets of human cells responding to infectious agents and immune modulators, the model produced a map of 104 expression programs, many enriched for signalling pathway genes and for targets bound by NF-$\kappa$B family transcription factors.

## Sources

- G. K. Gerber, R. D. Dowell, T. S. Jaakkola, D. K. Gifford, "Automated discovery of functional generality of human gene expression programs", PLoS Computational Biology 3 (2007), e148, <https://doi.org/10.1371/journal.pcbi.0030148> (PMC1941755), Results, "The GeneProgram model" (Figure 3) and Protocol S1.
- Y. W. Teh, M. I. Jordan, M. J. Beal, D. M. Blei, "Hierarchical Dirichlet processes", Journal of the American Statistical Association 101 (2006), 1566–1581, <https://doi.org/10.1198/016214506000000302>.
