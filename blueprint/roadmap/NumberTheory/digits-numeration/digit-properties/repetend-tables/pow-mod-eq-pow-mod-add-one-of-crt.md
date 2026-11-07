# Powers of $b^y \bmod p^i$ that differ by one

Let $p$ be a prime with $p \equiv 1 \pmod 6$,
let $i$ and $j$ be natural numbers with $j \ge 1$ and $i \ge 2j$, put $n = p^i$ and $Q = p^j$, and
let $b$ be a natural number whose multiplicative order modulo $n$ is $6Q$. Let $f \in \{1, -1\}$,
let $y$ be a natural number with $y \equiv s \pmod 6$ for some $s \in \{1, -1\}$, and put $e = 1$
if $sf = 1$ and $e = 5$ if $sf = -1$. Let $d$ be a natural number with $d \equiv 2f \pmod 6$, and
let $k < 6Q$ be a natural number with $k \equiv f \pmod 6$ and $k \equiv b^e d \pmod Q$. Then, with
$B = b^y \bmod n$, we have $B^k \bmod n = (B^d \bmod n) + 1$.

Here $b^5$ stands for $b^{-1}$ modulo $Q$, as $b^6 \equiv 1 \pmod Q$, so $b^e$ is $b^{sf}$ modulo
$Q$.

## Sources

- R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025), Article A26, Lemma 11 (`integers-2025-A26-lem-11`).
