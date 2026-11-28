# Constant-time d-ary cuckoo tables at load $(1-\varepsilon)c_d^*$

For every $d \ge 4$ and $\varepsilon \in (0,1)$, with $c_d^* = \xi_d / \big(d\,(1 - e^{-\xi_d})^{d-1}\big)$, where $\xi_d > 0$ is the unique solution of $d = \frac{\xi(e^{\xi} - 1)}{e^{\xi} - 1 - \xi}$, a $d$-ary cuckoo table with uniform random-walk insertion (variant (a), the walk analyzed by Bell and Frieze) at load factor $(1 - \varepsilon)c_d^*$ supports queries and deletions in at most $d$ probes in the worst case and insertions in $O_{d,\varepsilon}(1)$ expected time, with probability $1 - o(1)$ over the hash functions. The case $d = 3$ is not covered here: the cited refereed random-walk bounds for three hashes stop at the peeling threshold $c_3^{\Delta} \approx 0.818$, below the existence threshold $c_3^* \approx 0.918$.

## Proof sketch

Apply the Bell-Frieze bound for the uniform walk with $d \ge 4$ at $c = (1-\varepsilon)c_d^* < c_d^*$; queries inspect the $d$ candidate slots. For three hashes, Walzer's bound applies only at loads $c < c_3^{\Delta}$.

## Depends on

- [Peeling threshold of random hypergraphs](peeling-threshold.md)
- [d-ary cuckoo hashing and its hashing graph](d-ary-cuckoo-hashing.md)
- [Random-walk insertion for d-ary cuckoo hashing](random-walk-cuckoo-insertion.md)

## Proof depends on

- [Random-walk cuckoo insertion takes constant expected time up to the load threshold](bell-frieze-random-walk-bound.md)

## Sources

- Tolson Bell, Alan Frieze, "O(1) Insertion for Random Walk d-ary Cuckoo Hashing up to the Load Threshold", FOCS (2024), arXiv:2401.14394.
- Stefan Walzer, "Insertion Time of Random Walk Cuckoo Hashing below the Peeling Threshold", ESA (2022), arXiv:2202.05546.
