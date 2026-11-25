# Half-sib covariance of genotypic values

For real allele weights $p$ and genotypic values $G$ with [mean](mean-value.md) $\mu$, put

$$C_{HS} = \sum_{i, j, k, l} \sum_{b, b' \in \{1, 2\}} \frac{p_i p_j p_k p_l}{4}\, (G_{t_b k} - \mu)(G_{t_{b'} l} - \mu), \qquad t_1 = i,\ t_2 = j:$$

when $p$ is a probability vector, it is the covariance of the genotypic values of two half sibs under Hardy–Weinberg proportions: the common parent $(i, j)$ transmits independently to each offspring, and the second genes $k, l$ come from two unrelated mates.
