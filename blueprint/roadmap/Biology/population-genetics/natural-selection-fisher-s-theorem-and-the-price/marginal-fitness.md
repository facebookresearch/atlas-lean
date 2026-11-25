# Marginal fitness of an allele

For a finite set $\iota$ of alleles, a real vector $p$ on $\iota$, a real matrix $w$ of ordered genotype fitnesses and an allele $i$, the marginal fitness of $i$ is $m_i = \sum_j \frac{w_{ij} + w_{ji}}{2}\, p_j$. When $p$ is a probability vector, it is the mean fitness of a genotype carrying $i$ whose other allele is drawn from $p$, averaged over the two positions of $i$ in the ordered genotype.
