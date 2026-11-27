# Normalized score under stratification

In an [LD-score model](model.md) with $N$ individuals, for a real $N \times M$ genotype matrix $X$, a real number $s$ and $c \in \mathbb{R}^N$, the normalized score of marker $j$ under stratification is the function

$$\hat\beta_j = \frac{1}{N} \sum_{i=1}^{N} X_{ij}\, y_i$$

on $\Omega$, where $y$ is the [stratified phenotype](pheno-strat.md), with the convention $x/0 = 0$ when $N = 0$.
