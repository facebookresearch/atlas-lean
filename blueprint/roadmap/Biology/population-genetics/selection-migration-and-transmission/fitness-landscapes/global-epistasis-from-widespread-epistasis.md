# Global epistasis from widespread epistasis

Write a genotype–fitness map on $\ell$ biallelic loci $x_i \in \{-1, +1\}$ in its Fourier (Walsh) expansion

$$y = \bar y + \sum_i f_i x_i + \sum_{i>j} f_{ij} x_i x_j + \sum_{i>j>k} f_{ijk} x_i x_j x_k + \dots, \qquad (2)$$

with symmetric coefficients, where $\bar y$ is the average fitness over all genotypes. The fitness effect of the mutation $x_i = -1 \to +1$ on a background of fitness $y$ can be written exactly as

$$s_i = 2 f_i (1 - \tilde v_i) - 2 \tilde v_i (y - \bar y) + \tilde\epsilon_i, \qquad (3)$$

$$\tilde v_i = \frac{\big(\sum_{j \ne i} f_{ij}^2 + \sum_{j>k \ne i} f_{ijk}^2 + \dots\big) - \big(\sum_{j \ne i} f_j f_{ij} + \sum_{j>k \ne i} f_{jk} f_{ijk} + \dots\big)}{\sum_{j \ne i} (f_j - f_{ij})^2 + \sum_{j>k \ne i} (f_{jk} - f_{ijk})^2 + \dots}, \qquad (4)$$

where $\tilde\epsilon_i$ is a genotype-dependent term with mean zero across genotypes; the numerator of $\tilde v_i$ is proportional to the covariance of fitness effect and background fitness and the denominator to the variance of background fitness.

**Widespread-epistasis (WE) limit.** If locus $i$ has many independent nonzero epistatic terms and the additive effects of its partners are not much larger than the epistatic terms, then $\tilde\epsilon_i$ is approximately normal with variance proportional to $\tilde v_i(1 - \tilde v_i)$ and $\tilde v_i > 0$ typically, so fitness effects decline linearly with background fitness: diminishing returns for beneficial and increasing costs for deleterious mutations. Including both a mutation and its reversion,

$$s_i = -2 v_i (y - \bar y) + 2\sqrt{v_i(1 - v_i)}\, \eta_i, \qquad v_i = \frac{V_i}{V} = \frac{f_i^2 + \sum_{j \ne i} f_{ij}^2 + \dots}{\sum_k f_k^2 + \sum_{k>l} f_{kl}^2 + \dots}, \qquad (5),(6)$$

with $\eta_i$ normal of mean zero and variance $V$, the total variance of fitness across genotypes. The **variance fraction** $v_i$ is half the negative slope and also sets the residual scatter; for two loci the slope of the summed effect is governed by $v_{ij} = v_i + v_j - 2e_{ij}$, with $e_{ij}$ the epistasis between them of all orders.

## Depends on

- [Reciprocal sign epistasis, multiple peaks and the small-face limitation](epistasis-and-landscape-structure.md)

## Expansion

Heuristic: let $N$ of the coefficients be $\pm 1$ at random. Then $y = \bar y + N_+ - N_-$, and adaptation biases interactions towards positive ($N_+ > N_-$). A mutation at a locus involved in a fraction $v_i$ of the interactions flips on average $N_+ v_i$ positive and $N_- v_i$ negative ones, so $y_i = y - 2N_+v_i + 2N_-v_i = \bar y + (1 - 2v_i)(y - \bar y)$ and $s_i = -2v_i(y - \bar y)$; sampling fluctuations about this mean are Gaussian with magnitude $\sqrt{N v_i(1 - v_i)}$ for large $N$ with independent interactions. In general $\tilde v_i$ is positive if, keeping only pairwise terms, $\sum_{j\ne i} f_{ij}^2 > \sum_{j\ne i} f_j f_{ij}$; the left side grows like the number of partners $\ell$ while the right side, a sum of terms of random sign, grows like $\sqrt{\ell}$, so the trend is negative unless additive effects $a$ dominate epistatic ones $e$ with $a \gg e\sqrt{\ell}$. The prediction that residual variance is fixed by the slope distinguishes this mechanism from global epistasis produced by a nonlinearity applied to an additive trait. With epistasis $\sum_i v_i > 1$, since the variance contributions of different loci overlap.

## Sources

- G. Reddy and M. M. Desai, "Global epistasis emerges from a generic model of a complex trait", eLife 10 (2021), e64740, Results ("Diminishing-returns and increasing-costs epistasis", Equations 1–6), <https://doi.org/10.7554/eLife.64740>, PMCID: PMC8057814.
