# Karatsuba cost recurrence

The function $T$ on natural numbers defined by $T(n) = 1$ for
$n \le 1$ and $T(n) = 3\,T(\lceil n/2 \rceil) + n$ for $n \ge 2$.

It is the cost charged by Karatsuba multiplication on $n$ digits: one unit for a call with
$n \le 1$, and for $n \ge 2$ the three recursive calls on $\lceil n/2 \rceil$ digits plus a charge of $n$
units, an accounting convention for the linear digit work of the call.
