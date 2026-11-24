# Kahan compensated summation error bound

In binary floating-point arithmetic with round-to-nearest, precision $p$, unit roundoff $\varepsilon = 2^{-p}$, no overflow and no underflow, run Kahan's
compensated summation on $x_1, \dots, x_N$: $s = x_1$, $c = 0$, and for $j = 2, \dots, N$: $y = \mathrm{fl}(x_j - c)$,
$t = \mathrm{fl}(s + y)$, $c = \mathrm{fl}(\mathrm{fl}(t - s) - y)$, $s = t$. The result satisfies
$s = \sum_j x_j (1 + \delta_j) + O(N\varepsilon^2) \sum_j \lvert x_j \rvert$ with $\lvert \delta_j \rvert \le 2\varepsilon$ (Goldberg, Theorem 8),
where the $O$ term is a first-order summary; a version with explicit constants in place of the $O$ term is a separate
statement. For comparison, recursive summation $s = \mathrm{fl}(\cdots\mathrm{fl}(x_1 + x_2) \cdots + x_N)$ gives
$\sum_j x_j(1 + \delta_j)$ with $\lvert \delta_1 \rvert$ up to about $(N - 1)\varepsilon$ and $\lvert \delta_j \rvert$ up to about
$(N - j + 1)\varepsilon$ for $j \ge 2$ (Goldberg writes $(N - j)\varepsilon$), so perturbations as large as about $N\varepsilon$.

## Depends on

- [Round to nearest, ties to even](../floating-point-rounding/fl.md)

## Proof depends on

- [The relative error bound](../floating-point-rounding/abs-fl-sub-le.md)

## Sources

- What Every Computer Scientist Should Know About Floating-Point Arithmetic — D. Goldberg, ACM Computing Surveys 23(1), 1991, Theorem 8 (Kahan Summation Formula) and following paragraph; proof in the Appendix, after Knuth. <https://www.cs.tufts.edu/comp/40/docs/WhatEveryComputerScientistShouldKnowAboutFloatingPointArithmetic.pdf>
