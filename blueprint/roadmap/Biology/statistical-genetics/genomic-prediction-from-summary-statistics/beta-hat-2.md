# Normalized score in the stratified LD-score model

In a [stratified LD-score model](stratified-model.md) with $N$ individuals, and for a real $N \times M$ genotype matrix $X$, the normalized score of marker $j$ is the function

$$\hat\beta_j = \frac{1}{N} \sum_{i=1}^{N} X_{ij}\, y_i$$

on $\Omega$, where $y$ is the [phenotype](pheno.md), with the convention $x/0 = 0$ when $N = 0$.
