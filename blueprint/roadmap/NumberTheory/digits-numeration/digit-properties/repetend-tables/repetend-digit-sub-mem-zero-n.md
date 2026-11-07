# Digit differences for a base of order $6p^j$ modulo $p^i$

Let $p$ be a prime with
$p \equiv 1 \pmod 6$, let $i$ and $j$ be natural numbers, and put $n = p^i$ and $Q = p^j$. Let
$B < n$ be a natural number whose multiplicative order modulo $n$ is $6Q$, let $f \in \{1, -1\}$,
and let $d$ and $e$ be natural numbers with $d \equiv 2fQ \pmod{6Q}$ and $e \equiv fQ \pmod{6Q}$.
For natural $s$ write $r_s = \lfloor B^{s+1}/n \rfloor \bmod B$ for the $s$-th base-$B$ digit of
$1/n$, and put $D = n(r_e - r_d)$. Then $D = B + (B^{d+1} \bmod n) - (B^{e+1} \bmod n)$, and
$D = 0$ or $D = n$.

The statement is made for all natural numbers $i$ and $j$.

## Sources

- R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025), Article A26, Lemma 14 (`integers-2025-A26-lem-14`).
