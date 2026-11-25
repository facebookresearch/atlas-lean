# Two-locus Hudson simulator samples the two-locus ancestral process

Fix two loci, a population of constant size and scaled recombination rate $\rho \ge 0$ in the normalization of the [coalescent with recombination](coalescent-with-recombination-ancestral-material.md), with time scaled so that each pair of ancestors has a common-ancestor event at rate $1$. Hudson's algorithm keeps the current set of $k$ ancestors, each carrying ancestral material at one or both loci, $c$ of them at both. Recombination events occur at rate $c\rho/2$, the number of links between the two loci that lie within ancestral material times $\rho/2$, and split a uniformly chosen ancestor carrying both loci into an ancestor carrying $A$ only and one carrying $B$ only; common-ancestor events occur at rate $\binom k2$ and merge a uniformly chosen pair, coalescing the loci that both carry. A locus whose material has reached a single ancestor is removed. The sequence of states visited, with the times at which they change, has the law of the two-locus ancestral process, the two-locus case of the coalescent with recombination, and the joint law of the times $(T_A, T_B)$ to the most recent common ancestors of the two loci produced by the algorithm is the two-locus law. Equivalently, the algorithm may propose recombinations at rate $k\rho/2$ on uniformly chosen ancestors and ignore those that fall on an ancestor carrying a single locus.

## Depends on

- [Coalescent with recombination: ancestral-material state space and generator](coalescent-with-recombination-ancestral-material.md)

## Proof depends on

- [Hudson's algorithm without recombination samples the Kingman genealogy](../kingman-s-coalescent-and-watterson-s-estimator/hudson-s-algorithm-without-recombination-samples.md)

## Expansion

A full proof page must still establish:

- that the jump rates of the algorithm are those of the two-locus ancestral process, and that the thinned version with proposals at rate $k\rho/2$ has the same law;
- for $\rho = 0$, that the two marginal trees are identical and the algorithm reduces to the one-locus algorithm.

## Sources

- J. Kelleher, A. M. Etheridge and G. McVean, "Efficient coalescent simulation and genealogical analysis for large sample sizes", *PLOS Computational Biology* 12(5):e1004842, 2016, Hudson's algorithm (recombination at rate $\rho L/(m-1)$ over the available links $L$, common-ancestor events at rate $|P|(|P|-1)$ in the paper's time units), <https://ibg.colorado.edu/cdrom2019/evansL/simulation/papers/Kelleher%20et%20al.%202016%20MSPRIME%20coalescent%20simulation.PDF>
