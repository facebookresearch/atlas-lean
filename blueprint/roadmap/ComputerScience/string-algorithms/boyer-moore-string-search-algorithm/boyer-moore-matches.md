# Boyer–Moore matcher for all occurrences

Let $p = p_0 \cdots p_{m-1}$ and
$t = t_0 \cdots t_{n-1}$ be words over the alphabet $\{0, \dots, \sigma - 1\}$. The matcher
returns a list of offsets together with a cost. If $m = 0$ it returns $0, 1, \dots, n$ at cost
$n + 1$, and if $n < m$ it returns the empty list at cost $0$. Otherwise it charges $m + n$ for
converting $p$ and $t$ to arrays, computes the bad-character table $B$ and the strong
good-suffix table $G$ of $p$ with the Boyer–Moore preprocessing and charges the cost of that
preprocessing, and then visits alignments $s$, starting from $s = 0$, as long as
$s + m \le n$. At each alignment it charges $1$ and compares $p_r$ with $t_{s + r}$ for
$r = m - 1, m - 2, \dots, 0$, charging $1$ per comparison and stopping at the first mismatch.
If all $m$ letters agree, it records $s$, charges $2$ and moves to the alignment $s + G_0$. If
the first mismatch is at position $i$, it charges $1$ and moves to the alignment
$s + \max(G_i, B_c - m + 1 + i)$, where $c = t_{s + i}$ and the maximum is taken in the
integers. Finally it charges $1$ for each recorded offset and returns the recorded offsets in
the order they were found.

The result is every occurrence of $p$ in $t$, in increasing order and including overlaps. The
cost counts these selected events, not machine instructions.
