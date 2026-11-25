# Ancestry responsibility of an allele copy (E-step)

For a genotype matrix $g$, [admixture parameters](params.md) $\theta$, an individual $i$, a SNP $j$, a copy $c \in \{0, 1\}$ and a population $k$, the responsibility is

$$r_{ijck}(\theta) = \frac{p_\theta(o, k)}{\sum_{k' \in K} p_\theta(o, k')}, \qquad o = o_g(i, j, c),$$

the posterior probability that copy $c$ of $(i, j)$ descends from population $k$, where $p_\theta$ is the [joint weight](joint.md) and $o_g(i, j, c)$ the [observation of the copy](copy-allele.md) (with $x/0 = 0$).
