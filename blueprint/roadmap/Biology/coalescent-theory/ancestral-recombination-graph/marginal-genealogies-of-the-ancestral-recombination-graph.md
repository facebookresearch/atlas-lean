# Marginal genealogies of the ancestral recombination graph are Kingman coalescents

In the neutral ancestral recombination graph for $n$ sampled sequences, the marginal genealogy at any fixed genomic position — obtained by following, backward in time, the lineages carrying ancestral material at that position — is a Kingman coalescent on the $n$ sample copies (Hudson 1983; Griffiths and Marjoram 1997; as stated in Tavaré 2004, Sec. 10): recombination events do not change the number of lineages ancestral at that position, and each pair of them coalesces at rate $1$. Marginal genealogies at two positions are in general dependent, and their dependence decreases with the recombination distance; for two sequences the covariance of the two coalescence times is $(\rho + 18)/(\rho^2 + 13\rho + 18)$, which is Griffiths' (1981) result $F(0, 0, 2; \rho) = 4(\rho + 18)/(\rho^2 + 13\rho + 18)$ for the covariance of the two marginal tree lengths $L = 2T$ (Tavaré 2004, eq. (10.2.9)), with recombination rate $\rho/2$ per doubly ancestral lineage.

## Expansion

1. The marginal process at one position: the partition of the sample by ancestral lineages carrying material at that position.
2. Recombination as a relabelling that leaves this partition unchanged, and coalescence of two lineages carrying that position's material as a merger at rate $1$ per pair.
3. Equality in law with Kingman's partition-valued coalescent (via its [rate matrix](../../../Biology/coalescent-theory/partition-valued-kingman-coalescent/partition-rate.md)).
4. Two positions: the joint law, and the [two-locus covariance](../../../Biology/coalescent-theory/two-locus-coalescent/two-locus-cov.md) with its [path form](../../../Biology/coalescent-theory/two-locus-coalescent/covariance-coalescence-times.md).

## Sources

- S. Tavaré, Ancestral inference in population genetics, in *Lectures on Probability Theory and Statistics*, Lecture Notes in Math. 1837, Springer, 2004, 1–188.
- Original result: R. R. Hudson, Properties of a neutral allele model with intragenic recombination, Theor. Popul. Biol. 23 (1983), 183–201. <https://doi.org/10.1016/0040-5809(83)90013-8> The statement follows Tavaré (2004), Sec. 10.
- Original result: R. C. Griffiths and P. Marjoram, An ancestral recombination graph, in *Progress in Population Genetics and Human Evolution*, IMA Vol. Math. Appl. 87, Springer, 1997, 257–270. <https://doi.org/10.1007/978-1-4757-2609-1_16> The statement follows Tavaré (2004), Sec. 10.
