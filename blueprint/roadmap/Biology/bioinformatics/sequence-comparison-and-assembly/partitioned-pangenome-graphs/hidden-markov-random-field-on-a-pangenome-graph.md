# Hidden Markov random field on a pangenome graph

**Pangenome graph.** For $F$ gene families in $N$ genomes, the pangenome graph $G = (V, E)$ has a vertex $v_i$ for each family and an edge $i \sim i'$ whenever genes of families $i$ and $i'$ are adjacent in at least one genome, with weight

$$w_{i \sim i'} = \frac1N \sum_{j=1}^{N} \mathrm{countNeighboringGenes}(v_{i,j}, v_{i',j}),$$

the number of adjacencies between the two families across genomes divided by $N$.

**Model.** Latent partition labels $Z_1, \dots, Z_F \in \{1, \dots, K\}$ follow the Gibbs distribution

$$P(Z_1, \dots, Z_F) = W_\beta^{-1} \exp\!\Big(\sum_{i=1}^{F}\sum_{k=1}^{K} \pi_k\, \mathbf 1_{Z_i = k} + \beta\,\frac{F}{\sum_{i \sim i'} w_{i \sim i'}} \sum_{i \sim i'} w_{i \sim i'}\, \mathbf 1_{Z_i = Z_{i'}}\Big),$$

with spatial-regularity parameter $\beta \ge 0$ and normalizing constant $W_\beta$ (a sum over all $K^F$ labelings, not computable in practice). Conditional on the labels, the presence/absence rows are independent with the [multivariate Bernoulli](multivariate-bernoulli-mixture-of-gene-presence-absence-patterns.md) laws of their partitions:

$$P(X_1, \dots, X_F \mid Z) = \prod_{i=1}^{F}\prod_{j=1}^{N} \epsilon_{Z_i j}^{|x_{ij} - \mu_{Z_i j}|}(1 - \epsilon_{Z_i j})^{1 - |x_{ij} - \mu_{Z_i j}|}.$$

**Properties.**

- For $\beta = 0$ the labels are independent and the model reduces to the Bernoulli mixture (rows i.i.d.).
- For $\beta > 0$ the conditional law of $Z_i$ given all other labels depends only on the labels of its graph neighbours,

$$P(Z_i = k \mid Z_{-i}) \propto \exp\!\Big(\pi_k + \beta\,\frac{F}{\sum w} \sum_{i' \sim i} w_{i \sim i'}\,\mathbf 1_{Z_{i'} = k}\Big),$$

so a family is pulled toward the partition held by a weighted majority of its genomic neighbours (the Markov property); larger $\beta$ means stronger smoothing.
- The factor $F / \sum w$ normalizes the total coupling so that the strength of smoothing per family does not drift as the number of genomes, and hence the ratio of families to edge weight, changes.

Parameters are estimated by the neighbourhood EM (NEM) algorithm, which replaces the intractable posterior of $Z$ by a mean-field approximation; $K$ is chosen beforehand from the plain mixture.

## Depends on

- [Multivariate Bernoulli mixture of gene presence/absence patterns](multivariate-bernoulli-mixture-of-gene-presence-absence-patterns.md)

## Expansion

The local conditional follows by cancelling every term of the exponent that does not involve $Z_i$. Mean-field NEM iterates $\hat t_{ik} \propto \pi_k \exp\big(\beta\frac{F}{\sum w}\sum_{i' \sim i} w_{i\sim i'}\hat t_{i'k}\big)\, P(X_i \mid Z_i = k)$, alternating with M-steps for the Bernoulli parameters, which is the Bernoulli-mixture EM with responsibilities smoothed over the graph. The biological motivation is that variable (shell and cloud) genes cluster in genomic islands and hotspots, so neighbouring families tend to share a partition. Because NEM scales quadratically with the number of genomes, large collections are partitioned on random chunks of genomes (at least about 500 each) and a family is labelled by absolute majority over the chunks in which it appears.

## Sources

- G. Gautreau, A. Bazin, M. Gachet, et al., "PPanGGOLiN: depicting microbial diversity via a partitioned pangenome graph", PLoS Computational Biology (2020), Materials and Methods ("Pangenome graph", "Partitioning via Neighboring Expectation-Maximization", "Issues resulting from high-dimensional statistics and parallelization"), <https://doi.org/10.1371/journal.pcbi.1007732> (PMC7108747).
