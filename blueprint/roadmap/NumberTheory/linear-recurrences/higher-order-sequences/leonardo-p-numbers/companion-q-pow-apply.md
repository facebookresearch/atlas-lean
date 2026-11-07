# Entries of the powers of the companion matrix $Q_p$

Let $p \ge 2$ and $n$ be natural
numbers, and index the rows and columns of the $(2p+1) \times (2p+1)$ companion matrix $Q_p$ by
$0, 1, \dots, 2p$. Then for all indices $a$ and $b$, the entry $(a, b)$ of $Q_p^n$ equals
$A_p(n + 1 - b)$ if $a = 0$, equals $B_p(n - p + 1 + a - b)$ if $1 \le a \le p - 1$, and equals
$-A_p(n - (2p - a) - b)$ if $p \le a \le 2p$. Here $A_p, B_p : \mathbb{Z} \to \mathbb{Z}$ are the
sequences satisfying $S(t) = S(t-1) + S(t-p) - S(t-2p-1)$ for every integer $t$, with
$A_p(t) = 1$ for $1 \le t \le p$ and $A_p(t) = 0$ for $-p \le t \le 0$, and with $B_p(t) = 1$ for
$1 \le t \le p$ and for $t = -p+1$ and $B_p(t) = 0$ for the other $-p \le t \le 0$.

## Sources

- "On Generalized Leonardo `p`-Numbers", Journal of Integer Sequences 27 (2024), Article 24.4.6, Theorem 9.
