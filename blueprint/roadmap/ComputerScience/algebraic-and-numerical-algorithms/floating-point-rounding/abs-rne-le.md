# Bound on the rounded significand

Let $K$ be a linearly ordered field with a floor
function, let $p \ge 1$, let $x \in K$ be nonzero, and let
$e = \lfloor \log_2 |x| \rfloor - (p - 1)$ be the exponent of the last place of $x$. Then
$|\operatorname{rne}(x / 2^e)| \le 2^p$, where $\operatorname{rne}$ rounds to the nearest
integer, ties to even.

Since $|x / 2^e| < 2^p$, the value $2^p$ occurs only when rounding carries into the next
binade.
