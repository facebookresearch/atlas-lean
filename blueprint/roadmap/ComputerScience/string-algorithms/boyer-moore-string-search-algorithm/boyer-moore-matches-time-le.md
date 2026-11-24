# Worst-case cost of Boyer–Moore matching

Let $p$ and $t$ be words over the alphabet
$\{0, \dots, \sigma - 1\}$ of lengths $m$ and $n$. The cost of the Boyer–Moore matcher with
pattern $p$ and text $t$ is at most $n + 1$ if $m = 0$, at most $0$ if $n < m$, and at most
$\sigma + n + 11m - 6 + (m + 4)(n - m + 1)$ if $1 \le m \le n$.

The cost counts the matcher's selected events, not machine instructions. The bound is quadratic
and does not assert linear all-match comparison complexity or machine runtime.
