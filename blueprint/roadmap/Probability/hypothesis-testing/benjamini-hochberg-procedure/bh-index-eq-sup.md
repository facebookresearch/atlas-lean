# The Benjamini–Hochberg step-up index as a finite supremum

For real numbers $p_1, \dots, p_m$ and a real level $q$, the Benjamini–Hochberg step-up index, the largest $k \in \{0, \dots, m\}$ such that at least $k$ of the $p_i$ are at most $q k / m$, equals the finite supremum $\max_{k \le m} \bigl(k \text{ if } k \le \#\{i : p_i \le q k/m\}, \text{ else } 0\bigr)$. No range is assumed for the $p_i$ or $q$; the procedure applies it to p-values and a level in $[0, 1]$. For $m = 0$ the threshold $qk/m$ is $0$ by the convention for division by zero.
