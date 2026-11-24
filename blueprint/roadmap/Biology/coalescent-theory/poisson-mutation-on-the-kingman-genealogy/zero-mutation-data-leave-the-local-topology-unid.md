# Data with no segregating sites do not identify the topology of three genes

For a sample of $n = 3$ genes under Kingman's coalescent with infinitely-many-sites mutation at rate $\theta/2$ per lineage, the probability
of observing no segregating site given the genealogy $G$ is $e^{-(\theta/2) L(G)}$, where $L$ is the [total branch length](../kingman-s-coalescent-and-watterson-s-estimator/total-length.md), because the number of mutations
is [conditionally Poisson](has-cond-distrib-seg-sites-of-mutation.md) with mean $(\theta/2) L(G)$. The two genealogies $((1,2),3)$ and $((1,3),2)$ with the same coalescence heights
$t_a < t_{\mathrm{root}}$ have the same total length $t_a + 2t_{\mathrm{root}}$, and under [the law of the Kingman genealogy](../pairwise-differences-under-poisson-mutation/kingman-genealogy-measure.md) the ranked topology follows random joining, which for three genes is uniform over
the three labeled topologies, and is independent of the coalescence times. Hence, by [Bayes' rule](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/bayes-rule/posterior-eq-bayes-posterior.md), given zero segregating sites the posterior on the topology is
uniform, $\frac13$ each, and every estimator of the topology is correct with posterior probability exactly $\frac13$. Data with segregating
sites can break the symmetry: singletons in unequal numbers per leaf give unequal likelihoods.

## Depends on

- [The number of segregating sites is conditionally Poisson](has-cond-distrib-seg-sites-of-mutation.md)
- [Total branch length of a coalescent genealogy](../kingman-s-coalescent-and-watterson-s-estimator/total-length.md)
- [Law of the Kingman genealogy with random-joining topology](../pairwise-differences-under-poisson-mutation/kingman-genealogy-measure.md)

## Proof depends on

- [Bayes' rule for discrete observations](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/bayes-rule/posterior-eq-bayes-posterior.md)

## Sources

- J. F. C. Kingman, "The coalescent", Stochastic Processes and their Applications 13 (1982), 235–248, <https://doi.org/10.1016/0304-4149(82)90011-4> (exchangeability of the ranked topology). The statement is derived above.
