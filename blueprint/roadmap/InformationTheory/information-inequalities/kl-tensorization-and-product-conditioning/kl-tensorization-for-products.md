# Tensorization of KL divergence and product Pinsker bounds

Let $p_i, q_i$ ($i$ in a finite set $I$) be distributions on finite sets $X_i$ with $\mathrm{supp}\,p_i \subseteq \mathrm{supp}\,q_i$. Then, in nats,

$$
D\Big(\bigotimes_i p_i \,\Big\|\, \bigotimes_i q_i\Big) = \sum_i D(p_i \,\|\, q_i), \qquad D(p^{\otimes n} \,\|\, q^{\otimes n}) = n\, D(p\,\|\,q).
$$

Consequently the statistical distances satisfy $\delta(\bigotimes_i p_i, \bigotimes_i q_i) \le \sqrt{\frac12 \sum_i D(p_i\|q_i)}$ and $\delta(p^{\otimes n}, q^{\otimes n}) \le \sqrt{n D(p\|q)/2}$.

## Proof sketch

The log-likelihood ratio of a product is the sum of coordinate log-likelihood ratios, and the expectation of each summand under the product is the coordinate divergence. Pinsker's inequality $\delta \le \sqrt{D/2}$ applied to the products gives the distance bounds.

## Depends on

- [Kullback–Leibler divergence of finite probability laws](../../entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-to-measure.md)

## Proof depends on

- [Csiszár–Kullback–Pinsker inequality with zero entries allowed](../csiszar-kullback-pinsker-of-nonneg.md)

## Sources

- T. M. Cover and J. A. Thomas, "Elements of Information Theory", Wiley-Interscience, 2nd ed., 2006.
- A. B. Tsybakov, "Introduction to Nonparametric Estimation", Springer, 2009.
