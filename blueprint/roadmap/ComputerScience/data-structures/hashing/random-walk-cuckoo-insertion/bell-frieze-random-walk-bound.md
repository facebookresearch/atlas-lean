# Random-walk cuckoo insertion takes constant expected time up to the load threshold

Let $d \ge 3$, $c < c_d^*$ and $n = cm$. With probability $1 - o(1)$ over the random hash functions, the expected insertion time of random-walk insertion into a $d$-ary cuckoo table holding $n$ keys in $m$ slots is $O(1)$, a constant depending only on $c$ and $d$ but not on $m$. The bound is robust to $n^{\beta}$ oblivious insertions and deletions for a suitable constant $\beta > 0$.

## Proof sketch

Building on expansion properties of the bipartite hashing graph established by Fountoulakis, Panagiotou and Steger, Bell and Frieze introduce recursively defined sets $B_i$ of bad slots from which a random walk is unlikely to escape quickly, and show that below $c_d^*$ these sets are small and expand, so that from any slot the walk reaches a free slot within $\ell$ steps except with probability decaying geometrically in $\ell$. The geometric-tail lemma then bounds the mean.

## Depends on

- [Sharp load thresholds for d-ary cuckoo hashing](cuckoo-load-threshold.md)
- [Random-walk insertion for d-ary cuckoo hashing](random-walk-cuckoo-insertion.md)
- [A geometric tail bound gives constant expected walk length](geometric-tail-gives-constant-mean.md)

## Proof depends on

- [Sharp load thresholds for d-ary cuckoo hashing](cuckoo-load-threshold.md)
- [Random-walk insertion for d-ary cuckoo hashing](random-walk-cuckoo-insertion.md)
- [A geometric tail bound gives constant expected walk length](geometric-tail-gives-constant-mean.md)

## Sources

- Tolson Bell, Alan Frieze, "O(1) Insertion for Random Walk d-ary Cuckoo Hashing up to the Load Threshold", FOCS (2024), arXiv:2401.14394.
- Nikolaos Fountoulakis, Konstantinos Panagiotou, Angelika Steger, "On the Insertion Time of Cuckoo Hashing", SIAM Journal on Computing 42(6) (2013).
