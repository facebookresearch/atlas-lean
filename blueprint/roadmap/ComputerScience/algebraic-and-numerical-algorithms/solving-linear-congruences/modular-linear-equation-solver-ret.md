# Output of the modular linear equation solver

Let $a > 0$ and $n > 0$ be natural numbers,
$b$ an integer, $d = \gcd(a, n)$, and $y$ the coefficient of $a$ in the Bézout identity
$d = n u + a y$ computed by the extended Euclidean algorithm on $(n, a)$. If $d \mid b$, the list
returned by the modular linear equation solver on $a$, $b$, $n$ is $[x_0, x_1, \dots, x_{d-1}]$
with $x_i = \bigl((y \cdot (b / d)) \bmod n + i \cdot (n / d)\bigr) \bmod n$, where $r \bmod n$
denotes the least nonnegative residue of $r$; otherwise it is the empty list.
