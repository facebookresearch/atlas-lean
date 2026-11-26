# Pearson chi-square divergence

Let $p, q$ be discrete probability distributions on a countable set $X$. The *Pearson $\chi^2$ divergence* of $p$ from the reference $q$ is

$$
\chi^2(p \,\|\, q) = \sum_{x \in X} \frac{(p(x) - q(x))^2}{q(x)} \in [0, \infty],
$$

which equals $+\infty$ when the support of $p$ is not contained in that of $q$, and otherwise equals $\sum_x p(x)^2/q(x) - 1$. It is the $f$-divergence with $f(t) = (t-1)^2$, and $1 + \chi^2(p\|q) = M_2(p\|q) = e^{D_2(p\|q)}$ is the Renyi moment of order $2$.

## Depends on

- [f-divergence on a finite alphabet](../f-divergences/f-divergence.md)
- [Renyi divergence of discrete distributions](renyi-divergence.md)

## Sources

- A. B. Tsybakov, "Introduction to Nonparametric Estimation", Springer, 2009.
- C. L. Canonne, "Topics and Techniques in Distribution Testing: A Biased but Representative Sample", Foundations and Trends in Communications and Information Theory, 2022.
