# Expected association statistic in the stratified LD-score model

For every [stratified LD-score model](stratified-model.md) on a measure $\mu$ with categories $(C_c, \tau_c)$ and noise variance $\sigma_e^2$, every real $N \times M$ genotype matrix $X$ and every marker $j$,

$$\int \chi^2_j \, d\mu = N \sum_{c \in \mathcal{C}} \tau_c\, \ell(j, C_c) + \frac{\sigma_e^2}{N} \sum_{i=1}^{N} X_{ij}^2,$$

where $\chi^2_j$ is the [association statistic](chi-sq.md) and $\ell$ the [stratified LD score](strat-ldscore.md), with the convention $x/0 = 0$.
