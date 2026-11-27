# Bray-Curtis dissimilarity

For two communities described by non-negative abundance vectors $x, y \in \mathbb{R}_{\ge 0}^{S}$ over the same $S$ types, with $\sum_i x_i + \sum_i y_i > 0$, the Bray-Curtis dissimilarity is

$$\mathrm{BC}(x,y) = \frac{\sum_{i=1}^{S} |x_i - y_i|}{\sum_{i=1}^{S} (x_i + y_i)} = 1 - \frac{2\sum_{i=1}^{S} \min(x_i,y_i)}{\sum_{i=1}^{S}(x_i + y_i)} .$$

It satisfies $0 \le \mathrm{BC}(x,y) \le 1$, is symmetric, equals $0$ exactly when $x = y$, and equals $1$ exactly when the two communities share no type with positive abundance. It is invariant under a common positive rescaling of both vectors, $\mathrm{BC}(cx,cy) = \mathrm{BC}(x,y)$ for $c > 0$, and for vectors with equal totals $\sum_i x_i = \sum_i y_i = c > 0$ it equals the [total variation distance](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md) between the relative abundance distributions $x/c$ and $y/c$, which is half their $\ell^1$ distance:

$$\mathrm{BC}(x,y) = \frac{1}{2} \sum_{i=1}^{S} \Bigl|\frac{x_i}{c} - \frac{y_i}{c}\Bigr| = d_{TV}(x/c,\, y/c).$$

For example, $(1,0)$ and $(0,1)$ have $\mathrm{BC} = 1$ and total variation distance $1$.

## Depends on

- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Remarks

The index measures the fraction of total abundance that the two communities fail to share, which is exactly what the second form says: $\sum_i \min(x_i,y_i)$ is the shared mass, counted once in each community, and the remainder is unmatched. For equal totals the denominator is $2c$, and for measures on a finite set the supremum $\sup_B |\mu(B) - \nu(B)|$ is attained at $B = \{i : x_i > y_i\}$, where it equals $\frac12 \sum_i |\mu_i - \nu_i|$ because both distributions have total mass $1$. Normalizing by the combined total keeps the measure on $[0,1]$ and makes it insensitive to a change of units, but not to unequal sampling depth, so samples are rarefied or converted to relative abundance before comparison. Bray-Curtis is not a metric: the triangle inequality can fail, which is why it is used with ordination methods that accept a dissimilarity matrix rather than with procedures that require a metric embedding. It also ignores any relatedness among types, treating two distinct but closely related types as no more similar than two unrelated ones, which is the gap that phylogenetically weighted dissimilarities are built to close.

## Sources

- Human Microbiome Project Consortium. Structure, function and diversity of the healthy human microbiome. *Nature* 486:207-214 (2012), Figure 1B and Figure 2D, between-sample beta diversity. DOI <https://doi.org/10.1038/nature11234>. PMCID PMC3564958.
- Bray JR, Curtis JT. An ordination of the upland forest communities of southern Wisconsin. *Ecological Monographs* 27:325-349 (1957). DOI <https://doi.org/10.2307/1942268>.
