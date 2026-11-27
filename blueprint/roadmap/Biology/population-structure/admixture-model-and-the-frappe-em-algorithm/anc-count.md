# Expected ancestry count of an individual

Let $J$ be finite. For a genotype matrix $g$, [admixture parameters](params.md) $\theta$, an individual $i$ and a population $k$, the expected ancestry count is

$$A_{ik}(\theta) = \sum_{j \in J} \sum_{c \in \{0, 1\}} r_{ijck}(\theta),$$

where $r$ is the [responsibility](resp.md): the expected number of allele copies of $i$ descending from $k$.
