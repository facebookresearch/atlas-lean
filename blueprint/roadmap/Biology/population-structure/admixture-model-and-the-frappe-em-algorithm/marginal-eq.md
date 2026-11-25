# The marginal of an allele copy

For all [admixture parameters](params.md) $\theta$, individuals $i$, SNPs $j$ and $a$ true or false,

$$\sum_{k \in K} p_\theta((i, j, a), k) = \begin{cases} \phi_{ij}(\theta) & a \text{ true},\\ 1 - \phi_{ij}(\theta) & a \text{ false}, \end{cases}$$

where $p_\theta$ is the [joint weight](joint.md) and $\phi_{ij}$ the [reference-allele probability](qf.md).
