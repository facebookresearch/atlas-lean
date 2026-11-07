# Beta-function evaluation of hyperharmonic Euler sums

Let $k, p \ge 0$ be integers and
let $r, a$ be complex numbers with $\operatorname{Re}(r) < p + 1$ and $\operatorname{Re}(a) > -k$,
such that $r$ is not a positive integer and $a$ is not a nonpositive integer. Write
$H_n^{[r]}(k)$ for the generalized hyperharmonic number and let
$S(k, r; p + 1; a) = \sum_{n \ge k} H_n^{[r]}(k) / (n + a)^{p+1}$. Then

$$p! \, k! \, S(k, r; p + 1; a) = (-1)^p D_a^p D_r^k B(a, 1 - r),$$

where $B(a, 1 - r) = \Gamma(a) \Gamma(1 - r) \cdot (1/\Gamma)(a + 1 - r)$, with $1/\Gamma$ the
entire reciprocal of the Gamma function (zero at the poles of $\Gamma$), and $D_a^p D_r^k$ means
the $k$-th complex derivative in $r$ followed by the $p$-th complex derivative in $a$.

The source also states the identity at positive integers $r$, after removing the singularity of
$\Gamma(1 - r)$, and at nonpositive integers $a$, and extends it by analytic continuation; those
cases are not included here.

## Sources

- Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*, INTEGERS 26 (2026), Article A81, Theorem 1 (`integers-2026-A81-thm-1`).
