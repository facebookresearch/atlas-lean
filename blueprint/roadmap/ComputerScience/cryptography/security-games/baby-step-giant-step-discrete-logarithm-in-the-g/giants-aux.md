# Giant steps

Let $q > 1$. Labels are elements of $\mathbb{Z}/q$, compared by decidable equality, and a query either multiplies two labels or inverts one. The giant-step loop with fuel, index $i$, step count $m$, current label $\mathit{cur}$, table $\mathit{tab}$ and giant factor $\gamma$ is the oracle computation defined by recursion on the fuel:

- with fuel $0$ it makes no query and returns $\mathrm{none}$;
- with fuel $f + 1$ it [looks up](find-idx.md) $\mathit{cur}$ in $\mathit{tab}$ from index $0$. If it occurs, first at index $j$, it returns $\mathrm{some}((i m + j) \bmod q)$. Otherwise, if $i + 1 = m$ it returns $\mathrm{none}$; else it queries the product of $\mathit{cur}$ and $\gamma$ and, on answer $\mathit{nxt}$, continues with fuel $f$, index $i + 1$ and current label $\mathit{nxt}$.

So the loop can return $\mathrm{none}$ when its fuel runs out before index $m - 1$, and it stops without a query after an unmatched check at $i + 1 = m$.
