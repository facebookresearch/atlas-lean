# Tensorization and the mixture second-moment identity for chi-square divergence

Let $p_i, q_i$ ($i \in I$, $I$ finite) be distributions on finite sets $X_i$ and $\bigotimes$ denote independent products. Then

$$
1 + \chi^2\Big(\bigotimes_i p_i \,\Big\|\, \bigotimes_i q_i\Big) = \prod_{i}\big(1 + \chi^2(p_i \,\|\, q_i)\big),
$$

so $1 + \chi^2(p^{\otimes n}\|q^{\otimes n}) = (1 + \chi^2(p\|q))^n$. Moreover (Ingster-Le Cam), for a prior $\mu$ on a finite parameter set $T$, a family $(K_t)_{t \in T}$ of distributions on a finite set $X$ and a reference $q$ with $\mathrm{supp}\,K_t \subseteq \mathrm{supp}\,q$ for every $t \in \mathrm{supp}\,\mu$, the mixture $\bar K = \sum_t \mu(t) K_t$ satisfies

$$
1 + \chi^2(\bar K \,\|\, q) = \sum_{t, t' \in T} \mu(t)\mu(t') \sum_{x \in X}\frac{K_t(x) K_{t'}(x)}{q(x)},
$$

and for $n$ i.i.d. observations $1 + \chi^2\big(\sum_t \mu(t) K_t^{\otimes n} \,\|\, q^{\otimes n}\big) = \sum_{t,t'}\mu(t)\mu(t')\big(\sum_x K_t(x)K_{t'}(x)/q(x)\big)^n$.

## Proof sketch

Writing $1 + \chi^2(p\|q) = \sum_x p(x)^2/q(x)$, both sides of the product identity factor coordinatewise. For the mixture, expand $\bar K(x)^2 = \sum_{t,t'}\mu(t)\mu(t')K_t(x)K_{t'}(x)$ and exchange sums; the i.i.d. version applies the product identity to each inner sum.

## Depends on

- [Pearson chi-square divergence](chi-square-divergence.md)

## Sources

- A. B. Tsybakov, "Introduction to Nonparametric Estimation", Springer, 2009.
- C. L. Canonne, "Topics and Techniques in Distribution Testing: A Biased but Representative Sample", Foundations and Trends in Communications and Information Theory, 2022.
