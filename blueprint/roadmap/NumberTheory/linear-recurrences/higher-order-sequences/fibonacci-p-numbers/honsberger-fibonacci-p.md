# Honsberger identity for Fibonacci p-numbers

Let $p$, $m$ and $n$ be positive integers
with $p \le m + 1$ and $p \le n + 2$, and write $F_p(r)$ for the Fibonacci $p$-numbers. Suppose
that $F_p(0) = 0$, that $F_p(r) = 1$ for $1 \le r \le p$, and that
$F_p(r) = F_p(r-1) + F_p(r-p-1)$ for $r > p$ (these hold by definition). Then

$$F_p(m+1)\,F_p(n+2) + \sum_{i=1}^{p} F_p(m+1-i)\,F_p(n+i+1-p) = F_p(m+n+2).$$

All indices in the sum are natural numbers, since $i \le p \le m + 1$ and
$n + i + 1 \ge n + 2 \ge p$.

Proof: by strong induction on $m$ from a uniform form of the recurrence, with a telescoping
base case.

## Sources

- Binds source lines 425-449 with source-text SHA-256 `754dee8cf3e11595590ad2539aee76a3ad6d7ffcb80282b6a4488271f6392bd9`. From `https://cs.uwaterloo.ca/journals/JIS/VOL27/Kuhapatanakul/kuha13.tex`, source-file SHA-256 `dad9ca89271449561bda39a96e5705728a24469f6106405f6b2cc021c3d16524`, stable ID `jis_grounded_9dbbcac802edaa76c96bd1ff`. Corrected accounting: 2 mentions / 1 paper / 1 proof use. Excludes the downstream generalized Leonardo identity and the separate finite-sum identity. Definition from lines 79-85. Proves `Wanted` entry `honsberger_fibonacciP`.
