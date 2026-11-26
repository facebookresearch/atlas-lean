# Full-sib covariance of genotypic values

For real allele weights $p$ and genotypic values $G$ with [mean](mean-value.md) $\mu$, put

$$C_{FS} = \sum_{i, j, k, l} \sum_{b, b', e, e' \in \{1, 2\}} \frac{p_i p_j p_k p_l}{16}\, (G_{t_b s_e} - \mu)(G_{t_{b'} s_{e'}} - \mu),$$

with $t_1 = i$, $t_2 = j$, $s_1 = k$, $s_2 = l$: when $p$ is a probability vector, it is the covariance of the genotypic values of two full sibs under Hardy–Weinberg proportions: the unrelated sire $(i, j)$ and dam $(k, l)$ each transmit one gene to each of the two offspring independently.
