# The Bala–Somos parity conjectures

For a natural number $k$ let $p(k)$ be the number of
partitions of $k$. For natural numbers $m$ and $N$ let
$b_m(N) = \sum_{k=1}^{N} k^{2m+1} p(k) p(N-k)$ and $a(N) = \sum_{j=0}^{N} c(j)\, p(N-j)$, where
$c(0) = 0$ and $c(j) = \sum_{d \mid j,\ d \text{ odd}} (-1)^{j/d - 1}$ for $j \ge 1$. Then for all
$m \ge 1$ and $n \ge 1$: (a) if $n$ is odd, then $n$ divides $b_m(n)$; (b) $n$ divides $b_m(2n)$,
and $b_m(2n)/n$ is odd if and only if $n$ and $p(n)$ are both odd; (c) $a(n)$ is odd if and only
if $n$ and $p(n)$ are both odd; (d) twice the fractional part of the rational number $b_1(n)/n$
equals $1$ if and only if $n$ is even and $n/2$ and $p(n/2)$ are both odd.

Here $c(j)$ is the coefficient of $x^j$ in $\sum_{k \ge 1} x^{2k-1}/(1 + x^{2k-1})$, so $a(N)$ is
the coefficient of $x^N$ in $\bigl(\sum_{k \ge 1} x^{2k-1}/(1 + x^{2k-1})\bigr)
\prod_{k \ge 1} 1/(1 - x^k)$ (A305123). The paper calls the left side of (d) $c(n)$, a different
sequence from the coefficients $c(j)$ above.

## Sources

- Sela Fried, *Proofs of Ten Conjectures From the OEIS*, Journal of Integer Sequences 29 (2026), Article 26.1.8, Theorem 8 (`jis-2026-26.1.8-thm-8`).
