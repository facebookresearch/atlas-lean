# Canonical layout and correctness of quotient-filter updates

For a set $S$ and fingerprint functions $(q, r)$ there is exactly one slot configuration satisfying the quotient-filter invariant (runs sorted, in quotient order, each starting at the earliest free position not before its quotient, with consistent metadata bits). Insertion, which shifts the remainder of its cluster one slot to the right, and deletion, which shifts it left, map the canonical configuration of $S$ to the canonical configuration of $S \cup \{u\}$, respectively $S \setminus \{u\}$, provided $|S| < 2^b$. Consequently the filter has no false negatives on every hash seed, and its state depends only on the current set.

## Proof sketch

The invariant determines the slot of every remainder from the multiset of runs alone: runs are placed greedily in quotient order. An update changes one run, and shifting the rest of its cluster by one slot restores the greedy placement; metadata bits are recomputed locally at the cluster boundary.

## Depends on

- [Quotient filter](quotient-filter.md)

## Sources

- A. Pagh, R. Pagh and S. S. Rao, "An Optimal Bloom Filter Replacement", Proceedings of the 16th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2005.
- M. A. Bender, M. Farach-Colton, R. Johnson, R. Kraner, B. C. Kuszmaul, D. Medjedovic, P. Montes, P. Shetty, R. P. Spillane and E. Zadok, "Don't Thrash: How to Cache Your Hash on Flash", Proceedings of the VLDB Endowment 5(11), 2012.
