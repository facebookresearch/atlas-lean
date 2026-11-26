# Constant-time d-ary cuckoo tables at load $(1-\varepsilon)c_d^*$

For every $d \ge 3$ and $\varepsilon \in (0,1)$, a $d$-ary cuckoo table with random-walk insertion at load factor $(1 - \varepsilon)c_d^*$ supports queries and deletions in at most $d$ probes in the worst case and insertions in $O_{d,\varepsilon}(1)$ expected time, with probability $1 - o(1)$ over the hash functions. For $d = 3$ this exceeds both the peeling threshold $c_3^{\Delta} \approx 0.818$ and the binary threshold $1/2$ once $\varepsilon < 0.1$.

## Proof sketch

Apply the random-walk bound at $c = (1-\varepsilon)c_d^* < c_d^*$; queries inspect the $d$ candidate slots. The numerical comparison uses $c_3^* \approx 0.918$.

## Depends on

- [Random-walk cuckoo insertion takes constant expected time up to the load threshold](bell-frieze-random-walk-bound.md)
- [Peeling threshold of random hypergraphs](peeling-threshold.md)

## Proof depends on

- [Random-walk cuckoo insertion takes constant expected time up to the load threshold](bell-frieze-random-walk-bound.md)
- [Peeling threshold of random hypergraphs](peeling-threshold.md)

## Sources

- Tolson Bell, Alan Frieze, "O(1) Insertion for Random Walk d-ary Cuckoo Hashing up to the Load Threshold", FOCS (2024), arXiv:2401.14394.
- Stefan Walzer, "Insertion Time of Random Walk Cuckoo Hashing below the Peeling Threshold", ESA (2022), arXiv:2202.05546.
