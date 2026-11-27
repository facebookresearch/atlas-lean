# Likelihood-ratio Chernoff bound in Bhattacharyya and Hellinger form

Let $p, q$ be probability distributions on a countable set $X$, with Bhattacharyya coefficient $\mathrm{BC}(p,q) = \sum_x \sqrt{p(x)q(x)}$ and squared Hellinger distance $h^2(p,q) = 1 - \mathrm{BC}(p,q)$ (so $0 \le h \le 1$). If $x_1, \dots, x_n$ are i.i.d. from $p$, then

$$
\Pr\Bigl[\prod_{i=1}^n p(x_i) \le \prod_{i=1}^n q(x_i)\Bigr] \le \mathrm{BC}(p,q)^n \le \exp\bigl(-n\,h^2(p,q)\bigr).
$$

## Proof sketch

On the event, $\sqrt{\prod q(x_i)/\prod p(x_i)} \ge 1$, so by Markov's inequality its probability is at most $\mathbb{E}_p\sqrt{\prod_i q(x_i)/p(x_i)} = \mathrm{BC}(p,q)^n$ by independence. Finally $\mathrm{BC} = 1 - h^2 \le e^{-h^2}$.

## Depends on

- [Hellinger distance](../../../convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Proof depends on

- [Hellinger distance](../../../convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Sources

- Clément L. Canonne, "Topics and Techniques in Distribution Testing: A Biased but Representative Sample", Foundations and Trends in Communications and Information Theory, 2022.
- Alexandre B. Tsybakov, "Introduction to Nonparametric Estimation", Springer, 2009.
