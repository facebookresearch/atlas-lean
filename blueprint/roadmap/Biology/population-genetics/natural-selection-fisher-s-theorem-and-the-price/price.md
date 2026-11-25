# Price equation

Let $\iota$ be a finite set of individuals and $w$, $z$, $z'$ real vectors on $\iota$ with $\sum_i w_i \ne 0$: individual $i$ has fitness $w_i$, trait value $z_i$ and mean offspring trait value $z'_i$. Write $\mathbb{E}$ for the average over $\iota$, $\bar w = \mathbb{E}[w]$, $\bar z = \mathbb{E}[z]$, and $\bar z' = \sum_i w_i z'_i / \sum_i w_i$ for the fitness-weighted mean of the $z'_i$. Then

$$\bar w\,(\bar z' - \bar z) = \mathbb{E}\bigl[(w - \bar w)(z - \bar z)\bigr] + \mathbb{E}\bigl[w\,(z' - z)\bigr],$$

the population covariance of fitness and trait plus the expected fitness-weighted transmission change. The identity holds for signed $w$; when the $w_i$ are nonnegative reproductive weights (for instance offspring numbers) with positive total, $\bar z'$ is the mean trait of the offspring generation.

In the notation of [Hamilton's rule](../hamilton-s-rule/README.md), this is
$\bar w\, \Delta \bar z = \mathrm{Cov}(w, z) + \mathbb{E}[w\,(z' - z)]$, with
$\Delta \bar z = \bar z' - \bar z$ the [change in mean trait](../hamilton-s-rule/mean-trait-change.md),
$\mathrm{Cov}$ the [population covariance](../hamilton-s-rule/pop-cov.md) and
$\mathbb{E}[w\,(z' - z)]$ the [transmission term](../hamilton-s-rule/transmission.md).

## Sources

- G. R. Price, *Selection and covariance*, Nature 227 (1970), 520–521.
