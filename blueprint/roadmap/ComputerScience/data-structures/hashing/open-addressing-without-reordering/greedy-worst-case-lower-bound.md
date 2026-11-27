# Squared-logarithmic lower bound for greedy worst-case probes

Let $\delta \in (0, 1)$ be an inverse power of two with $\delta n$ an integer. In every greedy open-addressed hash table without reordering filled to $n - \delta n$ keys, the final insertion has expected probe complexity $\Omega(\log^2 \delta^{-1})$ (Theorem 4), so the worst-case expected probe complexity is $\Omega(\log^2 \delta^{-1})$. In the common range $\delta \ge n^{-o(1)}$ of this bound and the funnel hashing upper bound, funnel hashing is therefore optimal among greedy tables. Furthermore, for every open-addressed table without reordering (greedy or not), with probability greater than $1/2$ some key has probe complexity $\Omega(\log^2 \delta^{-1})$ (Theorem 6), and, when $1 - \delta = \Omega(1)$, some key has probe complexity $\Omega(\log^2 \delta^{-1} + \log \log n)$ (Theorem 7). Hence the high-probability worst-case probe complexity is $\Omega(\log^2 \delta^{-1} + \log \log n)$, matching the high-probability bound of funnel hashing in that common range.

## Proof sketch

For greedy tables the expected insertion costs $q_j$ are nondecreasing in $j$, so Yao's amortized $\Omega(\log \delta^{-1})$ bound forces some $1 \le i \le \log_2 \delta^{-1}$ for which the $(1 - 2^{-i})n$-th insertion costs at least $c\, i \log \delta^{-1}$ (Lemma 8). Condition on the set $S$ of occupied slots at that moment: later insertions behave like a greedy table on the $n/2^i$ free slots, the slots of $S$ deleted from every probe sequence, which by induction on $n$ forces second-layer cost $\sum_{j \le \log\delta^{-1} - i} c j$ on the final insertion, on top of the $c\, i\log\delta^{-1}$ probes needed to leave $S$. Together the final insertion costs at least $\sum_{j \le \log \delta^{-1}} c j = \Omega(\log^2 \delta^{-1})$. For the $\log\log n$ term, a scheme in which with probability greater than $1/2$ every key has probe complexity at most $d$ yields a $d$-choice balls-into-bins process on $m$ bins (ball $i$ goes to bin $h_j(k_i) \bmod m$ for its slot $h_j(k_i)$ when $j \le d$) whose fullest bin has $O(1)$ balls with probability greater than $1/2$; Vöcking's lower bound of $\Omega(\log\log n/d)$ for the fullest bin then forces $d = \Omega(\log\log n)$.

## Depends on

- [Open-addressing insertion without reordering](oa-without-reordering-model.md)
- [Greedy open addressing and uniform probing](greedy-open-addressing-and-uniform-probing.md)
- [Amortized, worst-case and high-probability probe complexity](amortized-and-worst-case-probe-complexity.md)
- [Funnel hashing layout](funnel-hashing-layout.md)

## Proof depends on

- [Funnel hashing: squared-logarithmic worst-case probes for a greedy table](funnel-hashing-bounds.md)
- [Maximum load of balls into bins](../../../randomized-algorithms/maximum-load-of-balls-into-bins.md)

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
