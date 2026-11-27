# Design matrix of stratified LD-score regression

Let $X$ be a real $N \times M$ genotype matrix and $a = (a_{kC})$ real annotation values indexed by markers and annotations $C$. The design matrix with a free intercept is the matrix with rows indexed by markers $j$ and columns indexed by an intercept column $\ast$ and the annotations $C$, with entries

$$D_{j\ast} = 1, \qquad D_{jC} = N\, \ell(j, C),$$

where $\ell$ is the [annotation LD score](annot-ldscore.md).
