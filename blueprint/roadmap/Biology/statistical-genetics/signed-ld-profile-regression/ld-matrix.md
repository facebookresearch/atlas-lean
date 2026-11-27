# In-sample LD matrix

For a real $N \times M$ genotype matrix $X$, the in-sample LD matrix is the $M \times M$ matrix

$$\hat R = \frac{1}{N} X^\top X, \qquad \hat R_{jk} = \frac{1}{N} \sum_{i=1}^{N} X_{ij} X_{ik},$$

with the convention $x/0 = 0$ when $N = 0$.
