# Indispensable digits

Let $x = (x_0, \dots, x_{n-1})$ be a $b$-ary string of length $n$,
written from left to right, and extend it by zero on the right, setting $x_j = 0$ for $j \ge n$.
A position $p < n$ is indispensable in $x$ when there is a natural number $r$ with
$1 \le r \le n + 1 - p$ such that $x_{p+t} = x_p$ for every $t$ with $1 \le t < r$, and
$x_{p+r} < x_p$. That is, some nonempty constant run of digits beginning at position $p$ is
followed on the right by a strictly smaller digit.

The paper writes the digit at position $p$ as $a_i$ with $i = n - p$ and prints the witness bound
$r \le i + 1$, although only the boundary digit $a_0$ (position $n$) is defined. With the zero
extension the final case $r = i + 1$ is unsatisfiable, so the predicate agrees with the source in
every case the source defines.
