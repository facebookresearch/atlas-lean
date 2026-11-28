# Elastic hashing: constant amortized and logarithmic worst-case probe complexity

Let $n \in \mathbb{N}$ and $\delta \in (0, 1)$ with $\delta \ge C/n$ for a suitable constant $C$ and $\delta^{-1}$ a power of two. Elastic hashing supports $n - \lfloor \delta n \rfloor$ insertions into an array of $n$ slots without reordering, with amortized expected probe complexity $O(1)$, worst-case expected probe complexity $O(\log \delta^{-1})$, and worst-case expected insertion time $O(\log \delta^{-1})$.

## Proof sketch

Each key inserted in batch $\mathcal{B}_i$ has expected probe complexity $O(1 + i)$ (Lemma 3). In the first case, with $A_i$ a $1 - \varepsilon$ fraction full, one of the $f(\varepsilon)$ probes into $A_i$ is free with probability $O(f(\varepsilon)\varepsilon)$, and the key then has probe complexity at most $\phi(i, f(\varepsilon)) = O(i f(\varepsilon)^2)$, contributing $O(i \varepsilon \log^6 \varepsilon^{-1}) = O(i)$. A key placed in $A_{i+1}$, which is at most $3/4$ full, uses $h_{i+1, j}$ with $j$ dominated by a geometric variable of mean $O(1)$, so it costs $O(\mathbb{E}[i j^2]) = O(i)$. The third (expensive) case occurs in batch $\mathcal{B}_i$ with probability $O(1/|A_i|^2)$ (Lemma 2) and costs $O(i |A_i|^2)$ in expectation. There are $O(\log \delta^{-1})$ batches, giving the worst-case bound, and the batch sizes decrease geometrically, giving the amortized bound. An insertion in the first two cases makes at most $f(\delta^{-1})$ probes in $A_i$ and $O(1)$ expected probes in $A_{i+1}$, so its insertion time is $O(\log \delta^{-1})$ (Lemma 4).

## Depends on

- [Elastic hashing layout and batch insertion rule](elastic-hashing-layout.md)
- [Amortized, worst-case and high-probability probe complexity](amortized-and-worst-case-probe-complexity.md)
- [Open-addressing insertion without reordering](oa-without-reordering-model.md)

## Proof depends on

- [Failure probability of a bounded number of uniform probes](bounded-probe-failure.md)
- [An injection of index pairs with cost $O(i j^2)$](pairing-injection-with-quadratic-weight.md)

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
