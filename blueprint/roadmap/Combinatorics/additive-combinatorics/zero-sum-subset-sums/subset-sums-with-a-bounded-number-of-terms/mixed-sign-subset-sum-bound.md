# Mixed-sign subset-sum bound

For natural numbers $n$, $p$, $\alpha$, $\beta$ (the numbers
of negative and positive elements of a set $A$, and the bounds on subset sizes), let
$\kappa = n + p - \beta$, computed in the integers, $T(x) = x(x+1)/2$ and
$S = T(p) + T(n) + 1$. The integer $L_{n,p}(\alpha, \beta)$, written $L(\alpha, \beta, A)$ in
the source, is $S - T(\beta - n) - T(\beta - p)$ if $1 \le \alpha < \kappa < n \le p$;
$S - T(\beta - n)$ if $1 \le \alpha < n \le \kappa < p$ or $1 \le \alpha = n < \kappa \le p$;
$S$ if $1 \le \alpha < n \le p \le \kappa$, or $1 \le \alpha = n < p < \kappa$, or
$1 \le \alpha = n = p < \kappa$; $S - T(\beta - n) - T(\alpha - n)$ if
$1 \le n < \alpha < \kappa \le p$; $S - T(\alpha - n)$ if $1 \le n < \alpha < p < \kappa$ or
$1 \le n < \alpha = p < \kappa$; $S - T(\alpha - n) - T(\alpha - p)$ if
$1 \le n \le p < \alpha < \kappa$; and $0$ otherwise.

These six cases are mutually exclusive, and when $1 \le n \le p$, $1 \le \alpha$ and
$\alpha + \beta + 1 \le n + p$ exactly one of them applies.

## Sources

- Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24 (2024), Article A116, Theorem 7 (definition of `L(α, β, A)`).
