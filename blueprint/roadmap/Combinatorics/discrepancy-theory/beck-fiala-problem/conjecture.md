# Linear Beck–Fiala conjecture

This is the statement that there is a real constant
$C > 0$ such that the following holds for all natural numbers $n$, $m$ and $t \ge 1$. Let
$S_1, \dots, S_n$ be subsets of $\{1, \dots, m\}$ such that each $S_i$ has at most $t$ elements,
each element of $\{1, \dots, m\}$ lies in at most $t$ of the sets $S_i$, and $S_i$ and $S_{i'}$
have at most one common element whenever $i \ne i'$. Then there are signs
$\varepsilon_1, \dots, \varepsilon_m \in \{1, -1\}$ such that
$\left|\sum_{j \in S_i} \varepsilon_j\right| \le C\sqrt{t}$ for every $i$.

In matrix terms: a $t$-sparse $0/1$ matrix (in rows and columns) in which every two rows share
at most one nonzero entry has discrepancy $O(\sqrt{t})$, improving the general bound
$O(\sqrt{t \log t})$.

## Sources

- AIM-COMBINATORICS-0044__20000919; AIM Hereditary discrepancy, item 1.7.
