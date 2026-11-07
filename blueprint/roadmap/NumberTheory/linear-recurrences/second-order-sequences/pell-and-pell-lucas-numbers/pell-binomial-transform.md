# Binomial transform of the Pell numbers

Let $P \colon \mathbb{N} \to \mathbb{Z}$ satisfy
$P_0 = 0$, $P_1 = 1$ and $P_{n+2} = 2 P_{n+1} + P_n$ for every $n$, so that $P_n$ is the
$n$-th Pell number. Then for every natural number $n$,

$$\sum_{i=0}^{n} \binom{n}{i} P_i = \sum_{k=0}^{n} \left(\frac{k}{8}\right) \binom{2n}{n+k},$$

where $\left(\frac{k}{8}\right)$ is the Kronecker symbol: it is $0$ for even $k$, $1$ for
$k \equiv \pm 1 \pmod 8$ and $-1$ for $k \equiv \pm 3 \pmod 8$.

Both sides give $0, 1, 4, 14, 48, 164, \dots$ (OEIS A007070) for $n = 0, \dots, 5$.

## Sources

- Greg Dresden and Yike Li, "Periodic Weighted Sums of Binomial Coefficients," Journal of Integer Sequences 26 (2023), Article 23.8.7, Corollary (equation e.12), lines 369–379, https://cs.uwaterloo.ca/journals/JIS/VOL26/Dresden/dresden26.tex
