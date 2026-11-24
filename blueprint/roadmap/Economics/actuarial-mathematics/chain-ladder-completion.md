# Chain-ladder completion of a run-off triangle

Let $C_{ij} \ge 0$ be cumulative claims for accident years $i$ and development years $j$ in $\{0, \dots, n\}$, observed when $i + j \le n$. Assume $\sum_{i < n - j}C_{ij} > 0$ for every $j < n$ (for $n = 0$ there is nothing to assume and nothing to forecast), and let $\hat f_j = \sum_{i < n-j}C_{i,j+1}/\sum_{i < n-j}C_{ij}$, both sums over the same accident years. The forward completion $\hat C_{i,n-i} = C_{i,n-i}$, $\hat C_{i,j+1} = \hat C_{ij}\hat f_j$ for $j \ge n - i$ satisfies $\hat C_{ij} = C_{i,n-i}\prod_{l = n-i}^{j-1}\hat f_l$ on every unobserved cell. If observed rows are nondecreasing, every $\hat f_j \ge 1$ and the implied reserves $\hat C_{in} - C_{i,n-i}$ are nonnegative.

## Sources

- T. Mack, "Distribution-free calculation of the standard error of chain ladder reserve estimates", *ASTIN Bulletin* 23(2):213–225, 1993, §2, estimators of f_k and ultimate claims, <https://www.casact.org/si/sites/default/files/2021-02/library_astin_vol23no2_213.pdf>
