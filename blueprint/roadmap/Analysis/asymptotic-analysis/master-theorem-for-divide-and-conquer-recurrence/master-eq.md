# Master theorem, critical case

Let $T$ satisfy a one-term Akra-Bazzi recurrence $T(n) = a\,T(r(n)) + g(n)$ for large $n$, with $a > 0$, $r(n) = n/b + O(n/\log^2 n)$, $g$ nonnegative with polynomial growth and $T$ positive on initial values. If $b > 1$, $c \ge 0$, $g(x) = \Theta(x^c)$ and $c = \log_b a$, then $T(n) = \Theta(n^c \log n)$; this includes the case $c = 0$, $a = 1$.
