# Hypergeometric over-representation test

Let a **population** of $N$ annotated genes contain $M$ members of a category $C$ ($0 \le M \le N$). An experiment selects a **list** of $n \le N$ genes, of which $k$ belong to $C$. Under the null hypothesis that the list is a uniformly random $n$-subset of the population, the number $X$ of category members on the list has the [hypergeometric law of marked items in a uniform random sample](../../../../Probability/distributions/discrete/hypergeometric-distribution/marked-items-in-a-uniform-random-sample.md), with $N$ items, $M$ marked and $n$ drawn.

The **over-representation p-value** of $C$ is the [one-sided Fisher exact p-value](../../../../Probability/hypothesis-testing/fisher-s-exact-test/fisher-upper-pvalue.md) of the $2 \times 2$ table (in $C$ or not) $\times$ (on the list or not), with group sizes $n_1 = M$ and $n_2 = N - M$ and success margin $t = n$, evaluated at the observed count $k$:

$$p_{\mathrm F}(k; N, M, n) = \Pr(X \ge k).$$

By the [tail-sum form of the Fisher p-value](../../../../Probability/hypothesis-testing/fisher-s-exact-test/fisher-upper-pvalue-eq-sum.md) it equals $\sum_{x = k}^{n} \binom{M}{x}\binom{N-M}{n-x} / \binom{N}{n}$, and it is $1$ at $k = 0$ and nonincreasing in $k$. Under the null it is the exact [upper-tail p-value](../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/upper-tail-pvalue.md) of $X$ under its own law, so it is [valid](../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue-upper-tail-pvalue.md): $\Pr(p_{\mathrm F}(X; N, M, n) \le \alpha) \le \alpha$ for every $\alpha \in [0,1]$.

## Depends on

- [Marked items in a uniform random sample](../../../../Probability/distributions/discrete/hypergeometric-distribution/marked-items-in-a-uniform-random-sample.md)
- [One-sided Fisher exact p-value](../../../../Probability/hypothesis-testing/fisher-s-exact-test/fisher-upper-pvalue.md)

## Proof depends on

- [The Fisher exact p-value as a hypergeometric tail sum](../../../../Probability/hypothesis-testing/fisher-s-exact-test/fisher-upper-pvalue-eq-sum.md)
- [Exact upper-tail p-value](../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/upper-tail-pvalue.md)
- [Validity of the upper-tail p-value](../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue-upper-tail-pvalue.md)

## Remarks

The test captures the granularity problem of rare categories: one category gene on a 50-gene list, when 60 of 10,000 array genes are in the category, looks like a 3.3-fold enrichment, yet $p_{\mathrm F} = 1 - \binom{9940}{50}/\binom{10000}{50} \approx 0.26$. Running the test over every category of an annotation system requires multiplicity control (the source uses bootstrap resampling of random gene lists).

## Sources

- D. A. Hosack, G. Dennis Jr, B. T. Sherman, H. C. Lane and R. A. Lempicki, "Identifying biological themes within lists of genes with EASE", Genome Biology 4 (2003) R70, Results (one-tailed Fisher exact probability of over-representation; worked example of a 50-gene list), <https://doi.org/10.1186/gb-2003-4-10-r70>, PMCID PMC328459.
