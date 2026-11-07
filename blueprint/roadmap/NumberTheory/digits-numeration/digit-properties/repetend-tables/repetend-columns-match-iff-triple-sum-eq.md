# Class B matched columns of repetend tables

Let $a \ge 1$ and $L = 12a + 6$, let $p$ be a
prime with $p \equiv 1 \pmod L$, let $k \ge 1$ and $n = p^k$, and let $b$ be a natural number of
multiplicative order $L$ modulo $n$; write $b_i = b^i \bmod n$. Let the rows be the integers $c$
with $1 \le c < n$, $\gcd(c, n) = 1$ and multiplicative order $L$ modulo $n$, and let column $j$
be the multiset of the digits $\lfloor c^{j+1}/n \rfloor \bmod c$ over these rows. Then
$\lfloor (b_i + b_{i + L/3} + b_{i + 2L/3})/n \rfloor = 1$ for every $0 \le i < L$ coprime to $L$
if and only if columns $2a + 1$ and $4a + 2$ are equal and columns $8a + 4$ and $10a + 5$ are
equal.

The proportion conjectured in the source is not stated here.

## Sources

- R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025), Article A26, Theorem 4 (`integers-2025-A26-thm-4`).
