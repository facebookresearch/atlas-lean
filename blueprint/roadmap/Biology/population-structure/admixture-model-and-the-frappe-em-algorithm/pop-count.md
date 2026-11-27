# Expected population count of a SNP

Let $I$ be finite. For a genotype matrix $g$, [admixture parameters](params.md) $\theta$, a population $k$ and a SNP $j$, the expected population count is

$$C_{kj}(\theta) = \sum_{i \in I} \sum_{c \in \{0, 1\}} r_{ijck}(\theta),$$

where $r$ is the [responsibility](resp.md): the expected number of allele copies at SNP $j$ descending from $k$.
