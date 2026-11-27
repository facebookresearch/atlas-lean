# Expected structural change in randomized incremental construction

Let $S = (X, \Pi, D, K)$ be a configuration space of dimension $d$ with $|X| = n$, and insert the elements of $X$ in uniformly random order. For $0 \le r \le n$ let $t_r$ be the expected value of $|T(R)|$ for a uniformly random $r$-element subset $R \subseteq X$. Then for $0 \le r < n$ the expected number of configurations created by the insertion of the $(r+1)$-st element, $\mathbb{E}[\deg(s, R \cup \{s\})]$, is at most $\dfrac{d}{r + 1}\, t_{r+1}$.

The proof is a backwards analysis: for a fixed $(r+1)$-set $Q$ the last element is uniform in $Q$, and $\sum_{s \in Q} \deg(s, Q) \le d\, |T(Q)|$ because each configuration has at most $d$ defining elements.

## Depends on

- [Configuration space](configuration-space.md)
- [Uniformly random rearrangement of a list](../../randomized-algorithms/average-case-running-time/uniform-permutation.md)

## Sources

- *Computational Geometry*, lecture notes, ETH Zürich, autumn 2013, Chapter 8 (The configuration space framework), <https://ti.inf.ethz.ch/ew/courses/CG13/lecture/Chapter%208.pdf>: Section 8.3 (expected structural change), the bound $\mathbb{E}(\deg(s, R \cup \{s\})) \le \frac{d}{r+1} t_{r+1}$ by the backwards movie and by the bijection $(R, s) \mapsto (R \cup \{s\}, s)$
