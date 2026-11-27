# Relative k-mer compositional diversity of a sequence

Let $s$ be a sequence of length $L$ over an alphabet of size $a$ (two in binary models, four for nucleic acids) and $1\le k<L$. Let $p_w$ be the frequency of the $k$-mer $w$ among the $L-k+1$ overlapping windows of $s$, and define the $k$-mer entropy

$$H_k(s)=-\sum_{w}p_w\log_2p_w .$$

Let $H_k^{\max}(L)$ be the largest value of $H_k$ over sequences of length $L$, and define the relative compositional diversity

$$C_k(s)=\frac{H_k(s)}{H_k^{\max}(L)}\in[0,1].$$

For a pool of molecules in which unique sequence $i$ makes up the fraction $n_i$ of molecules, the pool entropy is $D=-\sum_{i=1}^N n_i\log_2n_i$. Then:

1. $C_k(s)=0$ if and only if all $k$-mer windows of $s$ are identical, and $C_1$ is the normalized Shannon entropy of the base composition.
2. $H_k^{\max}(L)\le\log_2\min\bigl(a^k,\,L-k+1\bigr)$, with equality when $L-k+1\le a^k$, attained by a sequence whose windows are all distinct (a prefix of a de Bruijn sequence of order $k$).
3. $D=0$ exactly when all molecules are identical, and $D$ is maximal, $\log_2N$, when the $N$ unique sequences are equally abundant.

## Depends on

- [Shannon entropy](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)

## Proof depends on

- [A point mass has zero entropy](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy-pure.md)
- [Gibbs' inequality](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/shannon-entropy-le-cross-entropy.md)

## Expansion

Items 1 and 3 are the zero and maximum cases of Shannon entropy. For item 2, entropy is at most the logarithm of the support size, and the support of the window distribution has at most $a^k$ elements and at most $L-k+1$ windows. A de Bruijn sequence of order $k$ contains each $k$-mer exactly once as a cyclic window, so its linear prefixes of length up to $a^k+k-1$ have all windows distinct. The source defines $H_k^{\max}$ only as the maximum possible value and compares $C_k$ only between sequences of equal length; item 2 is supplied here. For $k>1$, $H_k$ distinguishes regular sequences that $H_1$ misses: an alternating binary sequence has maximal $H_1$ but $H_2$ near one bit rather than two.

In the source, $C_3$ (or $C_4$ for 50-mers) is the summary statistic: most of sequence space has high $C_k$, a tenfold monomer bias lowers average $C_4$ from about $0.94$ to $0.43$, known ribozymes of length 40 to 60 have average $C_4=0.970\pm0.013$, and in simulations of concatenation, template-directed ligation and hydrolysis the within-sequence $C_k$ and the pool entropy $D$ were highly correlated.

## Sources

- J. Derr, M. L. Manapat, S. Rajamani, K. Leu, R. Xulvi-Brunet, I. Joseph, M. A. Nowak and I. A. Chen, "Prebiotically plausible mechanisms increase compositional diversity of nucleic acid sequences", Nucleic Acids Research 40 (2012), 4711–4722, "Definitions and model" ("Measuring compositional bias for a given sequence", "Measuring diversity of a pool"), <https://doi.org/10.1093/nar/gks065> (PMC3378899).
