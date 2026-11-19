# Two-sided Hoeffding inequality for averages of bounded variables

Let $Z_1, \dots, Z_n$ be independent real random variables with $Z_i \in [a, b]$ almost surely. Then for every $t \ge 0$,

$$
\mathbb{P}\Big(\Big|\frac{1}{n} \sum_{i=1}^n Z_i - \frac{1}{n} \sum_{i=1}^n \mathbb{E}[Z_i]\Big| \ge t\Big) \le 2 \exp\Big(-\frac{2 n t^2}{(b - a)^2}\Big),
$$

with a quotient by $0$ read as $0$. The proof applies the one-sided bound to $Z_i$ and to $-Z_i \in [-b, -a]$ and takes a union bound.

This is the per-predictor step of the uniform deviation bound for a finite class of predictors in learning theory.

## Background

- [Uniform deviation of the empirical risk over a finite class](../../../ComputerScience/machine-learning/generalization-bounds-and-concentration/measure-real-exists-abs-empirical-risk-s.md): background, the application in statistical learning theory, a union bound of this inequality over the predictors.

## Sources

- F. Bach, *Learning Theory from First Principles*, MIT Press (2024); author PDF at <https://www.di.ens.fr/~fbach/ltfp_book.pdf>, Section 1.2.1, Corollary 1.1 (variables in $[0, 1]$) and the first remark after it (variables in $[a, b]$).
