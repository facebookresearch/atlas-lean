# Hamming-distance variance test of sample exchangeability and its large-$P$ chi-square limit

**Setting.** Let $\mathbf X \in \{0,1\}^{N\times P}$ be an individual-by-feature array (for example $N$ genomes at $P$ biallelic sites), rows $\mathbf x_1,\dots,\mathbf x_N$, with column sums $\mathbf c = (c_1,\dots,c_P)$. Population structure (stratification, admixture, cryptic relatedness) makes the rows non-exchangeable.

**ES&IF null hypothesis.** The rows are exchangeable and the features are independent. Equivalently, for independent permutations $\pi_1,\dots,\pi_P$ of $[N]$,
$$(\mathbf x_1,\dots,\mathbf x_N) \overset{d}{=} (\mathbf x_1^{\pi},\dots,\mathbf x_N^{\pi}), \qquad \mathbf x_i^{\pi} = (x_{\pi_1(i)1},\dots,x_{\pi_P(i)P}).$$
Conditionally on $\mathbf c$, the null law is uniform on $\mathcal Y_{\mathbf c} = \{\mathbf X' \in \{0,1\}^{N\times P}: \sum_i \mathbf x'_i = \mathbf c\}$, a set of size $\prod_{p=1}^P \binom{N}{c_p}$.

**Test statistic.** With Hamming distance $d_H(\mathbf x_i,\mathbf x_j) = \sum_{p=1}^P \mathbf 1(x_{ip} \ne x_{jp})$,
$$V^{(N,P)}(\mathbf X) = \frac{1}{P\binom N2}\sum_{i<j}\big(d_H(\mathbf x_i,\mathbf x_j) - \mu\big)^2, \qquad \mu = \frac{1}{\binom N2}\sum_{i<j} d_H(\mathbf x_i,\mathbf x_j).$$
This is the empirical variance of the pairwise distances. Large values reject ES&IF, and the p-value comes from resampling arrays by permuting each column independently.

**Theorem (large-$P$ limit).** Let $V^{(N,P)\ast}$ have the law of $V^{(N,P)}$ under the ES&IF null, conditional on the column sums. Then, as $P \to \infty$ with $N$ fixed,
$$V^{(N,P)\ast} \xrightarrow{d} V^{(N,\infty)} = \frac{a_1^N\,\chi^2_{N-1} + a_2^N\,\chi^2_{\binom{N-1}{2}-1}}{\binom N2},$$
where $\chi^2_{N-1}$ and $\chi^2_{\binom{N-1}2 - 1}$ are independent, and $a_1^N, a_2^N \ge 0$ are the large-$P$ limits of explicit functions of the column frequencies $c_p/N$.

**Theorem (rate).** For fixed $N$ there is a constant $C$, depending only on $N$, $a_1^N$ and $a_2^N$, such that
$$\sup_{t \ge 0}\Big|P\big(V^{(N,P)\ast} \le t\big) - P\big(V^{(N,\infty)} \le t\big)\Big| \le \frac{C}{\sqrt P}.$$

**Block-dependent features.** If the features split into $B$ mutually independent blocks with arbitrary dependence inside each block (for example linkage disequilibrium blocks), the null permutes whole blocks of columns. The same two-chi-square limit holds as $B, P \to \infty$, and the statistic needs only the per-block pairwise distances. Rejecting this null for a proposed LD partition means either the cohort is stratified or the blocks are not independent.

## Expansion

Write the centered pairwise-distance vector $(d_H(\mathbf x_i,\mathbf x_j) - \mu)_{i<j} \in \mathbb R^{\binom N2}$ as a sum over features of independent, conditionally centered contributions, one from each column's random permutation. A multivariate central limit theorem in $P$ makes it Gaussian, and its covariance is invariant under relabeling the $N$ individuals. The space of functions on pairs decomposes under the symmetric group into the trivial representation (dimension $1$), the standard representation (dimension $N-1$) and one further irreducible piece of dimension $\binom N2 - N = \binom{N-1}{2} - 1$. Centering removes the trivial part, and by Schur's lemma an invariant covariance is a scalar on each remaining piece, so the limit of the squared norm is $a_1\chi^2_{N-1} + a_2\chi^2_{\binom{N-1}2-1}$; this is the structure the degrees of freedom in the theorem reflect (the paper's full proof is in its supplement). A Berry–Esseen bound for sums of $P$ independent vectors gives the $O(P^{-1/2})$ rate. In practice the approximation is already accurate for $P \approx 50$, which replaces $R$ resamplings costing $O(N^2PR)$ by one numerical integration.

## Sources

- Alan J. Aw, Jeffrey P. Spence and Yun S. Song, "A simple and flexible test of sample exchangeability with applications to statistical genomics", arXiv:2109.15261 (2021), Section 2.1 (Definition 2.1, statistic and permutation null), Section 2.2 (Theorem 2.2), Section 4 (block-dependent features), Section 5.1 (Theorem 5.1) and Section 6.2 (LD splitting), <https://doi.org/10.48550/arXiv.2109.15261>.
