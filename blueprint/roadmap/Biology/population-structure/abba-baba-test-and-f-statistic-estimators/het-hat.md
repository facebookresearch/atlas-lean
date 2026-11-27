# Unbiased heterozygosity estimator

For a natural number $m$ (the number of sampled gene copies) and a real number $x$ (the number of derived copies), put

$$\hat h(m, x) = \frac{x (m - x)}{m (m - 1)},$$

with the convention $a/0 = 0$ (so $\hat h = 0$ for $m \le 1$).

For $m \ge 2$ and a derived-copy count $x$ with binomial law $\mathrm{Bin}(m, q)$, it is an [unbiased estimator](integral-het-hat.md) of $q(1 - q)$; for $m \le 1$ it is identically $0$.
