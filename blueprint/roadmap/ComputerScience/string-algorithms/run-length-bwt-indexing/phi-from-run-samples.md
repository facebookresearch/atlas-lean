# $\varphi$ is determined by $O(r)$ samples

Assume $T[n] = \$$ is a unique smallest end marker, so $\mathrm{SA}[1] = n$. Let $J$ be the set of BWT rows that are run starts other than row $1$, and let $Q = \{\mathrm{SA}[j] - 1 : j \in J,\ \mathrm{SA}[j] \ge 2\}$, a set of at most $r$ text positions. For every text position $i$ in the domain of $\varphi$, let $q$ be the smallest element of $Q$ with $q \ge i$; if it exists, then $\varphi(i) = \varphi(q) - (q - i)$. Hence storing $\varphi$ on $Q$ and a successor structure over $Q$, in $O(r)$ words, computes $\varphi$ in $O(\log\log_w(n/r))$ time.

## Proof sketch

Let $t$ be a text position whose row $j = \mathrm{ISA}[t]$ is not a run start and $j \ge 2$. Then $\mathrm{BWT}[j-1] = \mathrm{BWT}[j]$, so the LF-mapping sends rows $j-1$ and $j$ to consecutive rows, $\mathrm{LF}(j) = \mathrm{LF}(j-1) + 1$; since $\mathrm{SA}[\mathrm{LF}(j)] = t - 1$ and $\mathrm{SA}[\mathrm{LF}(j-1)] = \varphi(t) - 1$, this gives $\varphi(t-1) = \varphi(t) - 1$. Apply this for $t = i + 1, \dots, q$: none of these positions' rows is a run start until position $q + 1$, so $\varphi(i) = \varphi(q) - (q - i)$.

## Depends on

- [The function $\varphi$ on text positions](phi-function.md)
- [Suffix array](../../data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)
- [Burrows–Wheeler transform](../burrows-wheeler-transform-and-fm-index/bwt.md)
- [Number $r$ of runs in the Burrows–Wheeler transform](../string-attractors-and-repetitiveness-measures/bwt-run-count.md)

## Proof depends on

- [LF-mapping from the last column](../burrows-wheeler-transform-and-fm-index/lf.md)

## Sources

- Travis Gagie, Gonzalo Navarro, Nicola Prezza, "Fully Functional Suffix Trees and Optimal Text Searching in BWT-Runs Bounded Space", Journal of the ACM 67(1) (2020); SODA (2018), arXiv:1809.02792.
