# Benjamini–Hochberg FDR control for super-uniform nulls

Let $p_1, \dots, p_m$ be independent p-values, and let every true-null p-value $p_i$, $i \in H_0$, be
valid: $\Pr[p_i \le t] \le t$ for $t \in [0, 1]$. Then for $q \in [0, 1]$ the Benjamini–Hochberg
procedure at level $q$ has false discovery rate at most $q|H_0|/m$. Properly calibrated discrete
p-values, such as those of permutation or exact tests, are included, and nothing is assumed about the
false-null p-values beyond measurability and independence. For $m = 0$ both sides are $0$.

## Sources

- Benjamini and Hochberg (1995), Theorem 1, whose proof uses only $\Pr[p_i \le t] \le t$ for the true
  nulls.
