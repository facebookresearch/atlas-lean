# Class C matched columns of repetend tables

Let $p$ be a prime with $p \equiv 1 \pmod 6$,
let $j \ge 1$ and $i \ge 2j$, and put $n = p^i$, $Q = p^j$ and $L = 6Q$. Let $b$ be a natural
number of multiplicative order $L$ modulo $n$, and let $d, e < L$ be natural numbers with
$d \equiv b^2 \pmod Q$, $e \equiv b^4 \pmod Q$ and $d \equiv e \equiv 4 \pmod 6$. Let the rows be
the integers $c$ with $1 \le c < n$, $\gcd(c, n) = 1$ and multiplicative order $L$ modulo $n$, and
let column $s$ be the multiset of the digits $\lfloor c^{s+1}/n \rfloor \bmod c$ over these rows.
Then columns $d$ and $e$ are equal.

Theorem 6 of the source also says when the digit difference between these columns is $0$; that
clause is not stated here.

## Sources

- R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025), Article A26, Theorem 6 (`integers-2025-A26-thm-6`).
