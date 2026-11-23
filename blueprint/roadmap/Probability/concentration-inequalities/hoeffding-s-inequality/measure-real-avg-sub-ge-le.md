# Hoeffding's inequality for averages of bounded variables

Let $Z_1, \dots, Z_n$ be independent real random variables with $Z_i \in [a, b]$ almost surely. Then for every $t \ge 0$,

$$
\mathbb{P}\Big(\frac{1}{n} \sum_{i=1}^n Z_i - \frac{1}{n} \sum_{i=1}^n \mathbb{E}[Z_i] \ge t\Big) \le \exp\Big(-\frac{2 n t^2}{(b - a)^2}\Big),
$$

where a quotient by $0$ is read as $0$, so the bound is $1$ when $a = b$ (and when $n = 0$).

The proof specializes Hoeffding's lemma (a variable in $[a, b]$, once centered, is sub-Gaussian with parameter $(b - a)^2 / 4$) and Hoeffding's inequality for sums of independent sub-Gaussian variables to the normalization by $n$. With $[a, b] = [0, 1]$ it is the form in which the source states it.

## Background

- [Two-sided Hoeffding inequality for Bernoulli sums](hoeffding-bernoulli-sum-abs-tail.md): background, the special case of variables in $\{0, 1\}$ with a common mean.

## Sources

- F. Bach, *Learning Theory from First Principles*, MIT Press (2024); author PDF at <https://www.di.ens.fr/~fbach/ltfp_book.pdf>, Section 1.2.1, Proposition 1.2 (variables in $[0, 1]$) and the first remark after Corollary 1.1 (variables in $[a, b]$); W. Hoeffding, J. Amer. Statist. Assoc. 58 (1963), 13–30, Theorem 2.
