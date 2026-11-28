# Logarithmic lower bound for worst-case probes without reordering

In the high-load regime $1/n \le \delta \le 1/2$ with $\delta n$ an integer, every open-addressed hash table without reordering (greedy or not) that performs $n - \delta n$ insertions into an array of $n$ slots has worst-case expected probe complexity $\Omega(\log \delta^{-1})$. Hence elastic hashing is optimal for both amortized and worst-case expected probe complexity.

## Proof sketch

Let $c$ bound every key's expected probe complexity, so by Markov's inequality each key is placed within its first $2c$ probes with probability at least $1/2$. Consider the checkpoints $a_i = n(1 - 2^{-3i})$ for $i \le \alpha = \lfloor (\log_2 \delta^{-1})/3 \rfloor$, at which the free sets have geometrically decreasing sizes $n/8^i$. Farach-Colton, Krapivin and Kuszmaul build from them disjoint groups of slots $v_1, \dots, v_\alpha$ such that the first $2c$ probes of a key hit each $v_i$ $\Omega(1)$ times in expectation, because keys inserted near checkpoint $a_i$ must often land in the slots still free then. Hence $2c \ge \mathbb{E}[|\mathcal{H}_{2c}|] = \Omega(\alpha) = \Omega(\log \delta^{-1})$, where $\mathcal{H}_{2c}$ is the set of a key's first $2c$ probe positions (Theorem 5).

## Depends on

- [Amortized, worst-case and high-probability probe complexity](amortized-and-worst-case-probe-complexity.md)
- [Open-addressing insertion without reordering](oa-without-reordering-model.md)
- [Elastic hashing layout and batch insertion rule](elastic-hashing-layout.md)

## Proof depends on

- [Elastic hashing: constant amortized and logarithmic worst-case probe complexity](elastic-hashing-bounds.md)

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
