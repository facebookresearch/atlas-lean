# Normalized marker-phenotype scores in SLDP regression

In a [first-moment SLDP model](model.md) with $N$ individuals, and for a real $N \times M$ genotype matrix $X$, the vector of normalized marginal scores is the function $\hat\alpha : \Omega \to \mathbb{R}^M$ with

$$\hat\alpha_j = \frac{1}{N} \sum_{i=1}^{N} X_{ij}\, y_i,$$

where $y$ is the [phenotype](pheno.md), with the convention $x/0 = 0$ when $N = 0$. For $N > 0$, standardized markers and a phenotype with sample mean $0$ and unit sample standard deviation, these are the marginal correlations of the markers with the phenotype.
