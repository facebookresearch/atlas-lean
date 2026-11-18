# Filtering and subsampling as an inner product

For signals $h, x$ on $\mathbb{Z}/2N$,

$$\langle \tau_s h, x\rangle = \sum_k \overline{h[k - s]}\, x[k] .$$

At $s = 2n$ this is the subsampled filter output $(x \star \bar h)[2n]$ with $\bar h[k] = \overline{h[-k]}$, the analysis coefficient of the two-channel filter bank in Mallat's pyramidal algorithm (S. Mallat, *A theory for multiresolution signal decomposition: the wavelet representation*, IEEE Trans. Pattern Anal. Mach. Intell. 11 (1989)).
