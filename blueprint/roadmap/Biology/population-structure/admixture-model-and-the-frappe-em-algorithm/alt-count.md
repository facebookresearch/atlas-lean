# Expected alternative-allele count of a SNP per population

Let $I$ be finite. For a genotype matrix $g$, [admixture parameters](params.md) $\theta$, a population $k$ and a SNP $j$, the expected alternative count is

$$S_{kj}(\theta) = \sum_{i \in I} \sum_{c \in \{0, 1\},\ c \ge g_{ij}} r_{ijck}(\theta),$$

the sum of the [responsibilities](resp.md) over the copies that carry the alternative allele.
