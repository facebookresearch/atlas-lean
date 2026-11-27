# Karatsuba digit sizes and charge bound

Let $B \ge 2$, $n \ge 1$ and $x, y < B^n$, and let $h = \lceil n/2 \rceil$. Then $x$ and $y$ have at
most $n$ base-$B$ digits; the six split quantities $\lfloor x / B^h \rfloor$, $x \bmod B^h$,
$|\lfloor x / B^h \rfloor - x \bmod B^h|$ and the same three for $y$ (the operands of the three
recursive calls when $n \ge 2$) each have at most $h$ digits; and the declared charge of the
Karatsuba recursion is at most $9\, n^{\log_2 3}$. The charge bound holds for arbitrary operands,
so it is not a bound on the cost of actual digit arithmetic, division or intermediate operations.
