# Hypergeometric over-representation test

Let a **population** of $N$ annotated genes contain $M$ members of a category $C$ ($0 \le M \le N$). An experiment selects a **list** of $n \le N$ genes, of which $k$ belong to $C$. Under the null hypothesis that the list is a uniformly random $n$-subset of the population, the number $X$ of category members on the list is hypergeometric:
$$\Pr(X = x) = \frac{\binom{M}{x}\binom{N-M}{n-x}}{\binom{N}{n}}, \qquad \max(0, n-N+M) \le x \le \min(M,n).$$
The one-tailed Fisher exact probability of over-representation is
$$p_{\mathrm F}(k; N, M, n) = \Pr(X \ge k) = \sum_{x \ge k} \frac{\binom{M}{x}\binom{N-M}{n-x}}{\binom{N}{n}} .$$

**Properties.** $p_{\mathrm F}$ is nonincreasing in $k$, equals $1$ at $k = 0$, and is a valid p-value: $\Pr(p_{\mathrm F}(X) \le \alpha) \le \alpha$ under the null for every $\alpha \in [0,1]$. It is the one-sided Fisher exact test on the $2 \times 2$ table (on list or not) $\times$ (in $C$ or not), conditional on its margins.

## Depends on

- [With two colours the multivariate hypergeometric law is hypergeometric](../../statistical-genetics/association-tests/cochran-armitage-trend-test/mv-hypergeometric-real-fin-two.md)

## Expansion

Counting $n$-subsets with exactly $x$ category members gives the mass function; the upper tail is the probability of an outcome at least as extreme as the one observed. Validity follows because $p_{\mathrm F}(X) = 1 - F(X^-)$ for the null distribution function $F$, which is stochastically no smaller than uniform. The test captures the granularity problem of rare categories: one category gene on a 50-gene list, when 60 of 10,000 array genes are in the category, looks like a 3.3-fold enrichment, yet $p_{\mathrm F} = 1 - \binom{9940}{50}/\binom{10000}{50} \approx 0.26$. Running the test over every category of an annotation system requires multiplicity control (the source uses bootstrap resampling of random gene lists).

## Sources

- D. A. Hosack, G. Dennis Jr, B. T. Sherman, H. C. Lane and R. A. Lempicki, "Identifying biological themes within lists of genes with EASE", Genome Biology 4 (2003) R70, Results (one-tailed Fisher exact probability of over-representation; worked example of a 50-gene list), <https://doi.org/10.1186/gb-2003-4-10-r70>, PMCID PMC328459.
