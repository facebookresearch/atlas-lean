# Training genotype matrix with orthogonal standardized columns

A real $N \times M$ matrix $X$ has orthogonal standardized columns if

$$\sum_{i=1}^{N} X_{ik} X_{il} = \begin{cases} N & k = l,\\ 0 & k \ne l \end{cases}$$

for all columns $k, l$. For $N > 0$ and centred columns this says that the markers are uncorrelated, with unit sample variance, in the training sample.
