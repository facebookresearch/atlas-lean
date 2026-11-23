# Normalized marginal score in the LD-score model

In an [LD-score model](model.md) with $N$ individuals, and for a real $N \times M$ genotype matrix $X$, the normalized score of marker $j$ is the function

$$\hat\beta_j = \frac{1}{N} \sum_{i=1}^{N} X_{ij}\, y_i$$

on $\Omega$, where $y$ is the [phenotype](pheno.md), with the convention $x/0 = 0$ when $N = 0$. For a column with sum of squares $N$ it is the marginal least-squares estimate of the effect of marker $j$, whose denominator is $\sum_i X_{ij}^2$ in general.
