# Karatsuba multiplication

Karatsuba's algorithm on natural numbers $x$ and $y$, viewed as
$n$-digit numbers in base $B$, as a computation that returns a natural number together with a
cost. If $n \le 1$, it returns $xy$ at cost $1$. If $n \ge 2$, let $m = \lceil n/2 \rceil$, let
$a$ and $b$ be the natural-number quotient and remainder of $x$ by $B^m$, and let $c$ and $d$ be
those of $y$ by $B^m$. It runs itself with digit count $m$ on the pairs $(a, c)$, $(b, d)$ and
$(|a - b|, |c - d|)$, with results $e$, $f$ and $g$, and returns $B^{2m} e + B^m h + f$, where
$h = e + f - g$ (subtraction truncated at $0$) if $b \le a$ holds exactly when $d \le c$, and
$h = e + f + g$ otherwise. The cost of the call is $n$ plus the costs of the three recursive
calls.
