# Mixed-sign subset-sum bound with zero

For natural numbers $n$, $p$, $\alpha$, $\beta$
(the numbers of negative and positive elements of a set $A$ that also contains $0$, and the
bounds on subset sizes), let $\kappa = n + p + 1 - \beta$, computed in the integers,
$T(x) = x(x+1)/2$, $T_0(x) = x(x-1)/2$ and $S = T(p) + T(n) + 1$. The integer
$L^0_{n,p}(\alpha, \beta)$, written $L_0(\alpha, \beta, A)$ in the source, is
$S - T_0(\beta - n) - T_0(\beta - p)$ if $1 \le \alpha < \kappa < n \le p$;
$S - T_0(\beta - n)$ if $1 \le \alpha < n \le \kappa < p$ or $1 \le \alpha = n < \kappa \le p$;
$S$ if $1 \le \alpha < n \le p \le \kappa$, or $1 \le \alpha = n < p < \kappa$, or
$1 \le \alpha = n = p < \kappa$; $S - T_0(\beta - n) - T_0(\alpha - n)$ if
$1 \le n < \alpha < \kappa \le p$; $S - T_0(\alpha - n)$ if $1 \le n < \alpha < p < \kappa$ or
$1 \le n < \alpha = p < \kappa$; $S - T_0(\alpha - n) - T_0(\alpha - p)$ if
$1 \le n \le p < \alpha < \kappa$; and $0$ otherwise.

These six cases are mutually exclusive, and when $1 \le n \le p$, $1 \le \alpha$ and
$\alpha + \beta + 1 \le n + p + 1$ exactly one of them applies.

## Sources

- Raj Kumar Mistri, *Subset and Subsequence Sums with Bounded Numbers of Terms*, INTEGERS 24 (2024), Article A116, Theorem 8 (definition of `L₀(α, β, A)`).
