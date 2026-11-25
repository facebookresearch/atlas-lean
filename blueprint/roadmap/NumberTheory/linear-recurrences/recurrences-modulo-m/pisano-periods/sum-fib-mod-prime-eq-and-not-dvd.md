# Sum of the first $p$ Fibonacci numbers modulo a prime $p$

Let $p > 5$ be a prime, let
$F_i$ denote the $i$-th Fibonacci number, with $F_1 = F_2 = 1$, and let
$S = F_1 + F_2 + \dots + F_p$. If $p \equiv 1$ or $4 \pmod 5$, then $S$ leaves remainder $1$ on
division by $p$; if $p \equiv 2$ or $3 \pmod 5$, then $S$ leaves remainder $p - 2$ on division
by $p$; and in every case $p$ does not divide $S$.

The source prints the residues $3$ and $1$ for these two cases; the residues above are the
correct ones, since $S = F_{p+2} - 1$: for $p = 11$ one has $S = 232 \equiv 1 \pmod{11}$, and for
$p = 7$ one has $S = 33 \equiv 5 \pmod 7$.

## Sources

- Oisín Flynn-Connolly, "On the Divisibility of Sums of Fibonacci Numbers," INTEGERS 25 (2025), Article A87, Theorem 1.
