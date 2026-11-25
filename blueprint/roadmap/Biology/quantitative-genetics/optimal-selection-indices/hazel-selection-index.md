# Hazel's selection index

This node covers the following result. Let $H = a_1 G_1 + \dots + a_n G_n$ be the aggregate breeding value, with breeding values $G_i$ and economic weights $a_i$, and let $I = b_1 X_1 + \dots + b_n X_n$ be an index of phenotypic measurements $X_i$. Assume that $H$ and every $X_i$ have positive variance, that the correlation matrix $(r_{X_i X_j})$ of the $X_i$ is nonsingular, and that the vector of correlations $(r_{X_i H})_i$ is not zero. Then, among all weight vectors $b \neq 0$, the correlation $R_{IH}$ between $I$ and $H$ is largest exactly for the positive multiples of the multiple-regression coefficients of $H$ on $X$; with $\beta_i = b_i \sigma_{X_i} / \sigma_H$ these solve $\sum_j \beta_j r_{X_i X_j} = r_{X_i H}$ for $i = 1, \dots, n$. If instead every $r_{X_i H}$ is zero, every index with $b \neq 0$ is uncorrelated with $H$ and the equations give $b = 0$.

## Expansion

A good expansion replaces this node by planned pages beside it, each citing the source below:

1. The aggregate breeding value, the phenotypic index, and the correlations $r_{X_i X_j}$ and $r_{X_i H}$.
2. Maximization of $R_{IH}$ over nonzero weight vectors, by Cauchy–Schwarz in the inner product given by the phenotypic covariance, with the zero-correlation case stated separately.
3. The normal equations for the maximizing weights.

The source motivates the index by the expected progress from selection on $I$; relating that progress to $R_{IH}$ needs further assumptions (a selection intensity and a linear regression of $H$ on $I$) and is not part of this node.

Nothing beyond the statement above is claimed here.

## Sources

- L. N. Hazel, The genetic basis for constructing selection indexes, Genetics 28 (1943), 476–490. <https://doi.org/10.1093/genetics/28.6.476>
