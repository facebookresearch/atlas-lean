# Comparison hierarchy of total variation, Hellinger, KL and chi-square divergences

Let $p, q$ be distributions on a finite set with $\mathrm{supp}\,p \subseteq \mathrm{supp}\,q$. Let $\delta(p,q) = \frac12\sum_x |p(x) - q(x)|$ be the statistical distance, $\mathrm{BC}(p,q) = \sum_x\sqrt{p(x)q(x)}$ the Bhattacharyya coefficient, $h^2(p,q) = 1 - \mathrm{BC}(p,q)$ the squared Hellinger distance (normalized to lie in $[0,1]$), and $D(p\|q)$ the KL divergence in nats. Then

$$
4\,\delta(p,q)^2 \le \chi^2(p\,\|\,q), \qquad 2\,h^2(p,q) \le D(p\,\|\,q) \le \ln\big(1 + \chi^2(p\,\|\,q)\big) \le \chi^2(p\,\|\,q),
$$

and $e^{-D(p\|q)/2} \le \mathrm{BC}(p,q)$. Moreover $\chi^2$ satisfies data processing: $\chi^2(pK\|qK) \le \chi^2(p\|q)$ for every Markov kernel $K$.

## Proof sketch

Cauchy-Schwarz with weights $q(x)$ gives $(\sum_x |p(x)-q(x)|)^2 \le \chi^2(p\|q)$. Jensen's inequality for the concave logarithm under $p$ gives $-D/2 = \mathbb{E}_p[\ln\sqrt{q/p}] \le \ln \mathrm{BC}$, whence $D \ge -2\ln(1 - h^2) \ge 2h^2$, and $D = \mathbb{E}_p[\ln(p/q)] \le \ln \mathbb{E}_p[p/q] = \ln(1 + \chi^2)$. Data processing is the order-$2$ case of data processing for Renyi moments.

## Depends on

- [Pearson chi-square divergence](chi-square-divergence.md)
- [Kullback–Leibler divergence of finite probability laws](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-to-measure.md)
- [Hellinger distance](../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Proof depends on

- [Nonnegativity, data processing and adaptive composition of Renyi divergence](renyi-divergence-properties.md)

## Sources

- A. B. Tsybakov, "Introduction to Nonparametric Estimation", Springer, 2009.
- C. L. Canonne, "Topics and Techniques in Distribution Testing: A Biased but Representative Sample", Foundations and Trends in Communications and Information Theory, 2022.
