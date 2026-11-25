# Expected reference-allele count of a SNP per population

Let $I$ be finite. For a genotype matrix $g$, [admixture parameters](params.md) $\theta$, a population $k$ and a SNP $j$, the expected reference count is

$$R_{kj}(\theta) = \sum_{i \in I} \sum_{c \in \{0, 1\},\ c < g_{ij}} r_{ijck}(\theta),$$

the sum of the [responsibilities](resp.md) over the copies that [carry the reference allele](is-ref.md).
