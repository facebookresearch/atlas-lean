# Parent–offspring covariance of genotypic values

For real allele weights $p$ and genotypic values $G$ with [mean](mean-value.md) $\mu$, put

$$C_{PO} = \sum_{i, j, k} \sum_{b \in \{1, 2\}} \frac{p_i p_j p_k}{2}\, (G_{ij} - \mu)(G_{t_b k} - \mu), \qquad t_1 = i,\ t_2 = j:$$

when $p$ is a probability vector, it is the parent–offspring covariance of genotypic values under Hardy–Weinberg proportions: the parent has genotype $(i, j)$ and transmits $i$ or $j$ with probability $1/2$ each, and the offspring's other gene $k$ comes from an unrelated mate.
