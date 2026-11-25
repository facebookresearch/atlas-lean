# Overlap test with comparison count

For an interval $I$ with low endpoint $a$ and high
endpoint $b$ and an interval $J$ with low endpoint $c$ and high endpoint $d$, the instrumented
overlap test of $I$ against $J$ returns the pair (false, $1$) when $a > d$, the pair (false, $2$)
when $a \le d$ and $c > b$, and the pair (true, $2$) when $a \le d$ and $c \le b$; the number
is the count of endpoint comparisons evaluated.
