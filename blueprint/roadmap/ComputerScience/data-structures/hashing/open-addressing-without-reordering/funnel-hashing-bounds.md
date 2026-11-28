# Funnel hashing: squared-logarithmic worst-case probes for a greedy table

Let $n \in \mathbb{N}$ and $\delta \in (0, 1/2]$ with $\delta n$ an integer and $\delta \ge n^{-o(1)}$. Funnel hashing is a greedy open-addressing strategy that supports $n - \delta n$ insertions into an array of $n$ slots with worst-case expected probe complexity and insertion time $O(\log^2 \delta^{-1})$. Moreover, with probability $1 - 1/\mathrm{poly}(n)$, every key in the table has probe complexity $O(\log^2 \delta^{-1} + \log\log n)$, and the amortized expected probe complexity is $O(\log \delta^{-1})$ (Theorem 2).

## Proof sketch

A key probes one bucket of $\beta = O(\log\delta^{-1})$ slots in each of the $\alpha = \Theta(\log\delta^{-1})$ levels, so it makes at most $\alpha\beta = O(\log^2 \delta^{-1})$ probes before the overflow array. By a Chernoff bound on the number of attempts per bucket and McDiarmid's inequality, once a level has received $2|A_i|$ attempts it has fewer than $\delta|A_i|/64$ free slots with probability $1 - n^{-\omega(1)}$ (Lemma 5, using $\delta \ge n^{-o(1)}$); since the levels after $A_i$ hold more than $2.5|A_i|$ slots, fewer than $\delta n/8$ keys reach the overflow array (Lemma 6). There a key first makes at most $\log\log n$ uniform probes into the half $B$, whose load stays at most $1/2$, so it reaches the two-choice half $C$ with probability at most $1/\log n$; by the power-of-two-choices load bound no bucket of $C$ overflows with probability $1 - 1/\mathrm{poly}(n)$. An overflow insertion thus costs $O(1)$ expected and $O(\log \log n)$ worst-case probes, and the table succeeds with high probability.

## Depends on

- [Funnel hashing layout](funnel-hashing-layout.md)
- [Amortized, worst-case and high-probability probe complexity](amortized-and-worst-case-probe-complexity.md)
- [Greedy open addressing and uniform probing](greedy-open-addressing-and-uniform-probing.md)

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
