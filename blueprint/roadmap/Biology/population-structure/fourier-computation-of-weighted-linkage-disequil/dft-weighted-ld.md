# ALDER's Fourier-transform weighted LD computation

Let $S$ be a finite set of SNPs with grid cells $c$, genotypes $g_i(x)$ of $m$ individuals and weights $w$. For $N \ge 1$ and $j \in \mathbb{N}$, the transform computation is

$$\mathrm{WLD}^{\mathcal{F}}_j = \frac{1}{m - 1} \sum_{i=1}^{m} \mathrm{AC}_N(U^{(i)})(j),$$

where $U^{(i)}$ is the sequence of [cell totals](cell-sum.md) of the [centred weighted genotypes](centred-weighted.md) of individual $i$, $\mathrm{AC}_N$ the [autocorrelation via the discrete Fourier transform](autocorr-dft.md), $m - 1$ is computed in the complex numbers and $x/0 = 0$.
