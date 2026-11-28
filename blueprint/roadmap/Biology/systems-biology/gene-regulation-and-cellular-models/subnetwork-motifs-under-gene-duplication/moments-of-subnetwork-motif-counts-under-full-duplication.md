# Moments of subnetwork motif counts under full duplication

**Duplication process.** Start from $m$ genes, each the founder of its own gene family. At each step a gene chosen uniformly at random among all current genes is duplicated, and the copy joins the same family. After $n - m$ duplications the family sizes $\vec c = (c_1, \dots, c_m)$, $c_i \ge 1$, $\sum_i c_i = n$, form a composition of $n$ into $m$ parts.

**Proposition 1.** For given $m \le n$, all $\binom{n-1}{m-1}$ compositions of $n$ into $m$ parts are equally likely.

**Motifs.** A subnetwork motif $M$ is a gene-family-specific substructure on $k \le m$ families, say families $1, \dots, k$, whose original instance is the $k$ founders. Under **full duplication** every duplicated gene inherits all regulatory links, so every choice of one gene per family is an instance and $|M(n)| = c_1 c_2 \cdots c_k$.

**Theorem 1.** For $1 \le k \le m \le n$,

$$\mathbb E\,|M(n)| = \frac{\binom{n+k-1}{m+k-1}}{\binom{n-1}{m-1}} = \frac{\Gamma(n+k)\,\Gamma(m)}{\Gamma(n)\,\Gamma(m+k)} = \frac{(n+k-1)_k}{(m+k-1)_k},$$

with falling factorials $(a)_k$. If moreover $n \ge k^2$, then

$$\frac{n^k}{(m+k-1)_k} \le \mathbb E\,|M(n)| \le \frac{n^k}{(m+k-1)_k}\Big(1 + \frac{3k^2}{4n}\Big) \qquad \text{(Corollary 1)}.$$

**Second moment.** The same generating-function argument gives

$$\mathbb E\,|M(n)|^2 = \binom{n-1}{m-1}^{-1} \sum_{i=0}^{k} \binom{k}{i}\, 2^i \binom{n+k-1}{m+k+i-1},$$

and the variance vanishes exactly when $m = 1$, $m = n$, or $k = m = n - 1$ (then every composition has one part $2$ and $|M(n)| = 2$). The remark after Corollary 2 says the variance is nonzero outside $m=1$ and $m=n$; at $k=m=n-1$ every composition has one part equal to two and all others one, hence $|M(n)|=2$ always. These moments give the null mean and variance for significance tests of over-represented family-specific motifs in gene regulatory networks.

## Expansion

Proposition 1 is proved by induction on $n$: a composition is reached from $m$ predecessor compositions, the one with $c_i - 1$ in family $i$ being followed by a duplication in family $i$ with probability $(c_i - 1)/(n-1)$, and $\sum_i (c_i - 1) = n - m$ makes the uniform law self-reproducing; this is the Pólya urn with unit initial weights. For the moments, a sum over compositions of a product $\prod_i f_i(c_i)$ is the coefficient of $x^n$ in $\prod_i U_i(x)$ with $U_i(x) = \sum_{c \ge 1} f_i(c)x^c$. For the mean, families in $M$ contribute $\sum_c c\,x^c = x/(1-x)^2$ and the others $x/(1-x)$, so the sum is $[x^n]\, x^m(1-x)^{-(m+k)} = \binom{n+k-1}{m+k-1}$. For the second moment, families in $M$ contribute $\sum_c c^2x^c = x/(1-x)^2 + 2x^2/(1-x)^3$; expanding the $k$-th power binomially and extracting coefficients gives the stated sum. A stars-and-bars argument with $k$ extra "selector" bars gives a bijective explanation of the binomial in Theorem 1.

## Sources

- A. Scruse, J. Arnold, R. Robinson, "Counting Subnetworks Under Gene Duplication in Genetic Regulatory Networks", Bulletin of Mathematical Biology 88(3) (2026) 31, Proposition 1, Lemmas 1-3, Theorems 1-2 and Corollary 1, <https://doi.org/10.1007/s11538-025-01592-1>, PMCID PMC12832586.
