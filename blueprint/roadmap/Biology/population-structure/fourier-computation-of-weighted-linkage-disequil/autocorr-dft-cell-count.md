# Pair count as autocorrelation of cell occupancy counts

Let $S$ be a finite set of SNPs with grid cells $c$, and let $N \ge 1$ and $K$ be natural numbers with $c(x) < K$ for every $x$ and $2K \le N + 1$. Then for every $j < K$,

$$\mathrm{AC}_N(O)(j) = n_j,$$

where $O_k$ is the number of SNPs in cell $k$ (the [cell total](cell-sum.md) of the constant $1$), $\mathrm{AC}_N$ the [autocorrelation via the discrete Fourier transform](autocorr-dft.md) and $n_j$ the [number of pairs at offset $j$](pair-count.md).
