# Price equation

Let $\iota$ be a finite set of individuals and $w$, $z$, $z'$ real vectors on $\iota$ with $\sum_i w_i \ne 0$: individual $i$ has fitness $w_i$, trait value $z_i$ and mean offspring trait value $z'_i$. Write $\mathbb{E}$ for the average over $\iota$, $\bar w = \mathbb{E}[w]$, $\bar z = \mathbb{E}[z]$, and $\bar z' = \sum_i w_i z'_i / \sum_i w_i$ for the fitness-weighted mean of the $z'_i$. Then

$$\bar w\,(\bar z' - \bar z) = \mathbb{E}\bigl[(w - \bar w)(z - \bar z)\bigr] + \mathbb{E}\bigl[w\,(z' - z)\bigr],$$

the population covariance of fitness and trait plus the expected fitness-weighted transmission change. The identity holds for signed $w$; when the $w_i$ are nonnegative reproductive weights (for instance offspring numbers) with positive total, $\bar z'$ is the mean trait of the offspring generation.

## Sources

- G. R. Price, *Selection and covariance*, Nature 227 (1970), 520–521.
