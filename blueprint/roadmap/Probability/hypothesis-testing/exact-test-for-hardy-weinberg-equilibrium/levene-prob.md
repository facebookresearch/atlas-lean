# Levene's exact Hardy–Weinberg probability

Let $N, n_A, h \in \mathbb{N}$ and $n_B = 2N - n_A$. Levene's probability of $h$ heterozygotes among $N$ diploid individuals carrying $n_A$ copies of allele $A$ (and $n_B$ copies of $B$) under Hardy–Weinberg equilibrium is

$$L(N, n_A, h) = \frac{N!\, n_A!\, n_B!\, 2^h}{n_{AA}!\, h!\, n_{BB}!\, (2N)!}, \qquad n_{AA} = \frac{n_A - h}{2},\quad n_{BB} = \frac{n_B - h}{2},$$

when $h \le n_A$, $h + n_A \le 2N$ (that is, $h \le n_B$) and $n_A - h$ is even, and $L(N, n_A, h) = 0$ otherwise. The meaningful parameter domain is $n_A \le 2N$; for $n_A > 2N$ the value is $0$.
