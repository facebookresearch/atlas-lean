# Weak L^p limits of nonnegative functions are nonnegative

Let $1 < p < \infty$ and let $f_n$, $n \in \mathbb{N}$, and $f$ be real functions in $L^p([0, 1])$, for
Lebesgue measure, with $f_n \ge 0$ almost everywhere for every $n$. If $f_n$ converges weakly to $f$,
that is, $\ell(f_n) \to \ell(f)$ for every continuous linear functional $\ell$ on $L^p([0, 1])$, then
$f \ge 0$ almost everywhere.

## Idea

Weak limits keep pointwise signs. Test against the indicator $g$ of $\{f < 0\}$, which lies in
$L^q([0, 1])$ for the conjugate exponent $q$ because $[0, 1]$ has finite measure:
$\int f_n g \ge 0$ for every $n$, so $\int_{\{f < 0\}} f = \lim_n \int f_n g \ge 0$, which forces
$\{f < 0\}$ to be null. In other words, the nonnegative functions form a weakly sequentially
closed set.

## Statements

- [Weak $L^p$ limits of nonnegative functions are nonnegative](ae-nonneg-of-weak-tendsto-of-ae-nonneg.md)
