# LD score of a marker

For a real $N \times M$ genotype matrix $X$ and a marker $j$, the LD score of $j$ is

$$\ell_j = \sum_{k=1}^{M} r_{jk}^2,$$

where $r_{jk}$ is the [normalized cross product](ld-corr.md). For a [standardized](is-standardized.md) matrix this is the LD score of LD-score regression.
