# Tajima's D

For a natural number $n$ (the sample size) and real numbers $\pi$ (the mean number of pairwise differences) and $S$ (the number of segregating sites), Tajima's $D$ is

$$D = \frac{\pi - S / a_1}{\sqrt{e_1 S + e_2 S (S - 1)}},$$

where

- $a_1 = \sum_{i=1}^{n-1} \frac1i$ and $a_2 = \sum_{i=1}^{n-1} \frac{1}{i^2}$;
- $b_1 = \frac{n + 1}{3(n - 1)}$ and $b_2 = \frac{2(n^2 + n + 3)}{9n(n - 1)}$;
- $c_1 = b_1 - \frac{1}{a_1}$ and $c_2 = b_2 - \frac{n + 2}{a_1 n} + \frac{a_2}{a_1^2}$;
- $e_1 = \frac{c_1}{a_1}$ and $e_2 = \frac{c_2}{a_1^2 + a_2}$,

with the conventions $x/0 = 0$ and $\sqrt{x} = 0$ for $x \le 0$ (Tajima 1989). It is meaningful for $n \ge 4$ and $S \ge 1$, where the radicand is [positive](tajima-var-estimator-pos.md).

## Sources

- F. Tajima, *Statistical method for testing the neutral mutation hypothesis by DNA polymorphism*, Genetics 123 (1989), 585–595.
