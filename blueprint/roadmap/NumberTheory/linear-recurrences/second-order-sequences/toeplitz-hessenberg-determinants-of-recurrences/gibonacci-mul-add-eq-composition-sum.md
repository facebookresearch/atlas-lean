# Subsequences $G_{\ell n + m}$ of a Gibonacci sequence as composition sums

Let $y$ and $z$
be non-negative integers, not both zero, let $(G_k)$ be the Gibonacci sequence with $G_0 = y$
and $G_1 = z$, and let $L_k$ be the Lucas numbers. Let $\ell \ge 1$, $m \ge 0$ and $n \ge 1$, and
let $E$ be a complex number with $E^2 = (-1)^\ell G_\ell (G_\ell - L_\ell y) + y^2$ if $m$ is
even and $E^2 = (-1)^\ell G_{\ell+1} (G_{\ell+1} - L_\ell z) + z^2$ if $m$ is odd. Write
$A = L_\ell G_{\ell+m} - 2(-1)^\ell G_m + 2E$ and $B = (-1)^{\ell+1} G_m + E$, and assume that
$m \ge \ell + 2$ or $G_{\ell+m} B \ne 0$. Then

$$G_{\ell n + m} = \frac{A^{n-1}}{G_{\ell+m}^{n-2} B^n} \sum_c \left(-\frac{B^2}{A}\right)^{n-r}
\prod_{i=1}^{r} (E c_i - (-1)^\ell G_m),$$

where the sum runs over all compositions $c = (c_1, \dots, c_r)$ of $n$ (tuples of positive
integers with $c_1 + \dots + c_r = n$) and $r$ is the number of parts of $c$.

This is identity (35) of the source; for $0 \le m \le \ell + 1$ the condition $G_{\ell+m} B \ne 0$
is the source's sufficient condition.

## Sources

- Taras Goy and Mark Shattuck, *Determinantal Representations of Some Classical Recurrent Sequences*, INTEGERS 25 (2025), Article A97, Theorem 3 (`integers-2025-A97-thm-3`).
