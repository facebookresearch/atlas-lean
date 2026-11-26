# Constant random-walk insertion time below the peeling threshold

For every $d \ge 3$ and every fixed load factor $c < c_d^{\Delta}$, with probability $1 - o(1)$ over the hash functions, the expected insertion time of random-walk insertion into a $d$-ary cuckoo table at load $c$ is $O(1)$, a constant depending only on $c$ and $d$.

## Proof sketch

Below the peeling threshold the hashing graph peels completely, and the peeling order certifies, for every occupied slot, a short witness path to a free slot; Walzer shows that a random walk follows such witnesses with constant probability at each step, so its length has a geometric tail.

## Depends on

- [Peeling threshold of random hypergraphs](peeling-threshold.md)
- [Random-walk insertion for d-ary cuckoo hashing](random-walk-cuckoo-insertion.md)
- [d-ary cuckoo hashing and its hashing graph](d-ary-cuckoo-hashing.md)

## Sources

- Stefan Walzer, "Insertion Time of Random Walk Cuckoo Hashing below the Peeling Threshold", ESA (2022), arXiv:2202.05546.
