# Borders and periods of words

For a word $w$ of length $n$ and $0 \le k < n$, the prefix of length $k$ is also a suffix of $w$ (a **proper border** of length $k$) if and only if $d = n - k$ is a **period** of $w$, i.e. $w_i = w_{i+d}$ whenever $i + d < n$. The border lengths of $w$ form the chain $\pi(n), \pi(\pi(n)), \dots, 0$ obtained by iterating the prefix (failure) function $\pi$, and $\pi(q + 1)$ is obtained from this chain for the prefix of length $q$ as the largest border length $k$ with $w_k = w_q$, plus one (and $\pi(q + 1) = 0$ if there is no such $k$).

## Depends on

- [The KMP failure function](../knuth-morris-pratt-algorithm/mk-prefix-table-failure-spec.md)

## Sources

- D. E. Knuth, J. H. Morris Jr. and V. R. Pratt, "Fast Pattern Matching in Strings", SIAM Journal on Computing 6(2), 1977.
- M. Lothaire, "Combinatorics on Words", Cambridge University Press, 1997.
