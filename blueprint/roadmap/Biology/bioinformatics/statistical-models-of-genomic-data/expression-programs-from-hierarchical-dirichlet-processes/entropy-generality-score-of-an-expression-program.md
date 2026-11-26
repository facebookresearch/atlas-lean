# Entropy generality score of an expression program

Let an expression program $k$ be used by tissue groups $g = 1, \dots, G$ with total usages $u_{k1}, \dots, u_{kG} \ge 0$, not all zero (usage of a program by a group is the aggregated weight that group's samples put on the program). Normalise to the distribution $q_{kg} = u_{kg} / \sum_{h} u_{kh}$ and define the **generality score** of the program as the Shannon entropy

$$\mathcal G_k = -\sum_{g=1}^{G} q_{kg} \log q_{kg}, \qquad 0 \le \mathcal G_k \le \log G .$$

Then $\mathcal G_k = 0$ exactly when one group accounts for all the usage of the program (a program specific to a single group of tissues), and $\mathcal G_k = \log G$ exactly when the program is used equally by every group (a maximally general program). Normalising before taking the entropy makes the score invariant to the overall abundance of the program, so a program used weakly but evenly scores as general, and groups that barely use the program contribute little. Groups are required: computing the same entropy over individual tissue samples instead counts redundant related samples separately and overstates generality whenever the compendium contains several similar tissues.

## Depends on

- [Three-level hierarchical Dirichlet process model of expression programs](three-level-hierarchical-dirichlet-process-model-of-expression-programs.md)

## Proof depends on

- [Gibbs' inequality](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy-le-cross-entropy.md)
- [Equality in Gibbs' inequality](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/cross-entropy-eq-shannon-entropy-iff.md)
- [A point mass has zero entropy](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy-pure.md)

## Proof sketch

The bounds and their equality cases are the standard extremes of Shannon entropy on a finite simplex: entropy vanishes only at a point mass and is maximised only at the uniform distribution, by strict concavity of $-x\log x$ and Jensen's inequality. Invariance under scaling of $u_k$ is immediate from the normalisation. Because the grouping of samples and the number of groups are random in the hierarchical Dirichlet process model, the score is averaged over posterior samples rather than computed once. In the map of 104 expression programs that Gerber et al. inferred from 62 time-series data sets of cells responding to infection, low-scoring programs were used by few host-cell and infection types and were proposed as candidates for drug targets with little cross-talk, while high-scoring programs tracked common inflammatory responses.

## Sources

- G. K. Gerber, R. D. Dowell, T. S. Jaakkola, D. K. Gifford, "Automated discovery of functional generality of human gene expression programs", PLoS Computational Biology 3 (2007), e148, <https://doi.org/10.1371/journal.pcbi.0030148> (PMC1941755), Results, "The generality score naturally categorized programs into a spectrum of responses to infection", and Protocol S1.
