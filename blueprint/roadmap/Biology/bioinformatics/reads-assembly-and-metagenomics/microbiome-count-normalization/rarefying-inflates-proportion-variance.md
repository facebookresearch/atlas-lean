# Rarefying inflates the variance of proportion estimates

Fix a library of $n$ reads in which each read independently belongs to a given taxon with probability $p \in [0,1]$, so the taxon count is $K \sim \mathrm{Binomial}(n, p)$. **Rarefying** to depth $m \in \{1,\dots,n\}$ draws $m$ of the $n$ reads uniformly without replacement and records the taxon count $X$ among them, so that

$$X \mid K \sim \mathrm{Hypergeometric}(n \text{ reads},\ K \text{ of the taxon},\ m \text{ drawn}).$$

Compare the full-data proportion $\hat p = K/n$ with the rarefied proportion $\tilde p = X/m$.

**Theorem.**

1. $X \sim \mathrm{Binomial}(m, p)$, so $\tilde p$ is unbiased with $\operatorname{Var}(\tilde p) = p(1-p)/m$.
2. $\mathbb{E}[\tilde p \mid K] = \hat p$, and

$$\operatorname{Var}(\tilde p) = \operatorname{Var}(\hat p) + \frac{(n-m)\,p(1-p)}{m\,n} = \frac{n}{m}\,\operatorname{Var}(\hat p).$$

3. For every convex loss $\ell$, $\mathbb{E}\,\ell(\hat p, p) \le \mathbb{E}\,\ell(\tilde p, p)$. Under squared-error loss the inequality is strict whenever $m < n$ and $0 < p < 1$, so the rarefied estimator is dominated by the full-data estimator and is inadmissible.

## Depends on

- [Marked items in a uniform random sample](../../../../Probability/distributions/discrete/hypergeometric-distribution/marked-items-in-a-uniform-random-sample.md)

## Proof depends on

- [Variance of the binomial law](../../../../Probability/distributions/discrete/binomial-distribution/variance-id-map-cast-binomial.md)
- [Mean of the hypergeometric distribution](../../../../Probability/distributions/discrete/hypergeometric-distribution/sum-mul-hypergeometric-real.md)
- [Variance of the hypergeometric distribution](../../../../Probability/distributions/discrete/hypergeometric-distribution/sum-sq-sub-mean-mul-hypergeometric-real.md)
- [Rao–Blackwell inequality for one law](../../../../Probability/statistical-estimation/rao-blackwell-theorem/integral-comp-cond-exp-le.md)

## Proof sketch

(1) Choosing $m$ reads at random from $n$ independent Bernoulli$(p)$ reads yields $m$ independent Bernoulli$(p)$ reads. (2) The hypergeometric mean is $mK/n$, and its variance is $m\frac{K}{n}\big(1-\frac{K}{n}\big)\frac{n-m}{n-1}$; using $\mathbb{E}[K(n-K)] = n(n-1)p(1-p)$ gives $\mathbb{E}\operatorname{Var}(X \mid K) = m(n-m)p(1-p)/n$, and the law of total variance gives the formula. (3) Since $\hat p = \mathbb{E}[\tilde p \mid K]$, conditional Jensen gives $\ell(\hat p,p) \le \mathbb{E}[\ell(\tilde p,p) \mid K]$; this is Rao–Blackwellization of $\tilde p$ on the sufficient statistic $K$. The factor $n/m$ is the variance cost: rarefying a library of 1000 reads to 100 multiplies the variance of each proportion by 10, which is the minimal two-sample example of the source. Rarefying equalizes variances across libraries only by raising all of them to the worst one, adds randomization noise, and discards whole samples below the cutoff. When reads are overdispersed across biological replicates (the negative binomial model), the same conditional-expectation argument applies within each sample, and the remedy is to model the counts with size factors rather than subsample them.

## Sources

- P. J. McMurdie and S. Holmes, "Waste not, want not: why rarefying microbiome data is inadmissible", PLoS Computational Biology 10 (2014) e1003531, Introduction, subsection "Statistical motivation" (two-sample example, Figure 1) and Text S1, <https://doi.org/10.1371/journal.pcbi.1003531>, PMCID PMC3974642.
