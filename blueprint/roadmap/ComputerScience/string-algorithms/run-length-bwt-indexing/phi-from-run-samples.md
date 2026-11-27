# $\varphi$ is determined by $O(r)$ samples

Assume $T[n] = \$$ is a unique smallest end marker, so $\mathrm{SA}[1] = n$. Let $J$ be the set of BWT rows that are run starts, row $1$ included, and let $Q = \{\mathrm{SA}[j] - 1 : j \in J,\ \mathrm{SA}[j] \ge 2\}$, a set of at most $r$ text positions. For $n \ge 2$ it contains $n - 1 = \mathrm{SA}[1] - 1$. For every text position $i \le n - 1$, let $q$ be the smallest element of $Q$ with $q \ge i$, which therefore exists; then $\varphi(i) = \varphi(q) - (q - i)$. Hence storing $\varphi$ on $Q$, the single value $\varphi(n) = \mathrm{SA}[n]$, and a successor structure over $Q$, in $O(r)$ words, computes $\varphi$ in $O(\log\log_w(n/r))$ time. The sample from row $1$ cannot be dropped: sampling only the other run starts gives the same positions $\{2\}$ and the same value $\varphi(2) = 5$ for $\mathtt{baab}\$$ and $\mathtt{babb}\$$, but $\varphi(3) = 2$ in the first and $\varphi(3) = 1$ in the second. Gagie, Navarro and Prezza instead sample the text positions at both ends of every BWT run and use a predecessor search.

## Proof sketch

Let $t$ be a text position whose row $j = \mathrm{ISA}[t]$ is not a run start, so $j \ge 2$. Then $\mathrm{BWT}[j-1] = \mathrm{BWT}[j]$, so the LF-mapping sends rows $j-1$ and $j$ to consecutive rows, $\mathrm{LF}(j) = \mathrm{LF}(j-1) + 1$; since $\mathrm{SA}[\mathrm{LF}(j)] = t - 1$ and $\mathrm{SA}[\mathrm{LF}(j-1)] = \varphi(t) - 1$, this gives $\varphi(t-1) = \varphi(t) - 1$. Apply this for $t = i + 1, \dots, q$: if the row of such a $t$ were a run start, then $t - 1 \in Q$ with $i \le t - 1 < q$, contradicting the choice of $q$; so $\varphi(i) = \varphi(q) - (q - i)$. Since $\mathrm{BWT}[j-1] = \mathrm{BWT}[j]$ and the end marker occurs once, $\mathrm{SA}[j-1] \ge 2$, so $\varphi(t) - 1$ above is a text position.

## Depends on

- [The function $\varphi$ on text positions](phi-function.md)
- [Suffix array](../../data-structures/tries-and-integer-dictionaries/suffix-array/suffix-array.md)
- [Burrows–Wheeler transform](../burrows-wheeler-transform-and-fm-index/bwt.md)
- [Number $r$ of runs in the Burrows–Wheeler transform](../string-attractors-and-repetitiveness-measures/bwt-run-count.md)

## Proof depends on

- [LF-mapping from the last column](../burrows-wheeler-transform-and-fm-index/lf.md)

## Sources

- Travis Gagie, Gonzalo Navarro, Nicola Prezza, "Fully Functional Suffix Trees and Optimal Text Searching in BWT-Runs Bounded Space", Journal of the ACM 67(1) (2020); SODA (2018), arXiv:1809.02792, Lemma 3.
