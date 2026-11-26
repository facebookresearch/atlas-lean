# Bottom-up table of the weighted interval scheduling recurrence

For intervals indexed by
the positive integers with start times $s$, finish times $f$ and weights $w$, the table for $j$ is
a pair of arrays $(M_0, \dots, M_j)$ and $(P_0, \dots, P_j)$ with $M_0 = P_0 = 0$ and, for
$1 \le i \le j$, $P_i$ the result of the binary search for the last index $m \le i - 1$ with
$f(m) \le s(i)$, starting from $[0, i - 1]$, and $M_i = \max(M_{i-1}, w(i) + M_{P_i})$. Each entry
charges the comparisons of its binary search and one unit for the comparison of weights.
