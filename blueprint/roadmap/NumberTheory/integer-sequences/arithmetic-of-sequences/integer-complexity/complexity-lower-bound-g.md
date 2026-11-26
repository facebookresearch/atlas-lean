# Lower-bound function for integer complexity

For a natural number $n$, let $a$ be the
largest natural number with $3^a \le n$ when $n \ge 1$, and let $a = 0$ when $n = 0$. The function
$g$ on the natural numbers is given by $g(n) = 3a$ if $n < \frac{4}{3} \cdot 3^a$,
$g(n) = 3a + 1$ if $\frac{4}{3} \cdot 3^a \le n < 2 \cdot 3^a$, and $g(n) = 3a + 2$ if
$n \ge 2 \cdot 3^a$.
