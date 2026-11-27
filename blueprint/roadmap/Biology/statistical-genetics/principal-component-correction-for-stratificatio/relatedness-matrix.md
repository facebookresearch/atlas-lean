# Patterson's relatedness matrix

For a real $N \times M$ genotype matrix $C$ with [normalized matrix](normalized-genotype.md) $\tilde C$, Patterson's relatedness matrix is the $N \times N$ matrix

$$\Psi = \frac{1}{M}\, \tilde C \tilde C^\top,$$

with the convention $0^{-1} = 0$ (so $\Psi = 0$ when $M = 0$). Its top eigenvectors are the axes of variation.
