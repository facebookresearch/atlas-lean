# Admissible ternary strings

For natural numbers $b$ and $n$, the strings $w$ over
$\{0, 1, 2\}$ of length $n - 1$ (truncated subtraction, so length $0$ when $n = 0$) such that
every segment of $w$ obtained by cutting at its zeros (before the first zero, between
consecutive zeros and after the last zero, empty segments included) either consists only of
$1$s and has length at least $b - 1$, or consists only of $2$s and has length at least $b$.
In particular an empty segment is allowed exactly when $b \le 1$.

This is the segment form of the conditions in Theorem 2 of Hopkins and Wang (no $12$ or $21$
subwords, run-length bounds, and separation of successive zeros).
