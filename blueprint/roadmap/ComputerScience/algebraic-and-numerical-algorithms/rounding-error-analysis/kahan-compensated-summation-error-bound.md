# Kahan compensated summation error bound

In binary floating-point arithmetic with round-to-nearest, precision $p$, unit roundoff $\varepsilon = 2^{-p}$, no overflow and no underflow, run Kahan's
compensated summation on $x_1, \dots, x_N$: $s = x_1$, $c = 0$, and for $j = 2, \dots, N$: $y = \mathrm{fl}(x_j - c)$,
$t = \mathrm{fl}(s + y)$, $c = \mathrm{fl}(\mathrm{fl}(t - s) - y)$, $s = t$. The result has the form $s = \sum_j x_j (1 + \delta_j) + r$, where every
summand is perturbed by a relative error $\lvert \delta_j \rvert \le 2\varepsilon$, independent of $N$, and $r$ is a remainder of second order in $\varepsilon$
(Goldberg, Theorem 8). Recursive summation, by contrast, perturbs early summands by relative errors that grow linearly in $N$.

## Expansion

This page becomes ready once these prerequisites are stated:

- An explicit bound on the remainder $r$, of the form $\lvert r \rvert \le C(N, \varepsilon) \sum_j \lvert x_j \rvert$ with all constants given, together with the hypothesis on $N\varepsilon$ under which it holds (statement prerequisite; not yet stated)
- The matching explicit bound for recursive summation, with relative errors bounded in terms of $(N - j + 1)\varepsilon$ (statement prerequisite; not yet stated)

## Depends on

- [Round to nearest, ties to even](../floating-point-rounding/fl.md)

## Proof depends on

- [The relative error bound](../floating-point-rounding/abs-fl-sub-le.md)

## Sources

- What Every Computer Scientist Should Know About Floating-Point Arithmetic — D. Goldberg, ACM Computing Surveys 23(1), 1991, Theorem 8 (Kahan Summation Formula) and following paragraph; proof in the Appendix, after Knuth. <https://www.cs.tufts.edu/comp/40/docs/WhatEveryComputerScientistShouldKnowAboutFloatingPointArithmetic.pdf>
