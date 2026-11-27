# Canonical layout and correctness of quotient-filter updates

For a set $S$ with $|S| < 2^b$ and fingerprint functions $(q, r)$ there is exactly one slot configuration satisfying the quotient-filter invariant (runs sorted, stored in quotient order, each starting at the first slot not before its quotient that is not used by earlier runs, with metadata bits as defined). Insertion of $u \notin S$, which places $r(u)$ in its run and shifts every later remainder of the cluster one slot to the right, up to and including the first empty slot, maps the canonical configuration of $S$ to that of $S \cup \{u\}$ when $|S| + 1 < 2^b$; deletion of $u \in S$, which removes $r(u)$ and shifts the later remainders of its run and the later runs of its cluster one slot to the left, stopping at an empty slot or at a run that already starts at its own quotient, maps the canonical configuration of $S$ to that of $S \setminus \{u\}$. Consequently the filter has no false negatives for every choice of the hash functions, and its state depends only on the current set. The invariant and the shifting updates are those of Bender et al. (Section 3); keeping each run sorted is the convention that makes the configuration unique, since the source does not order remainders within a run.

## Proof sketch

The invariant determines the slot of every remainder from the multiset of fingerprints alone: runs are placed greedily in quotient order around the circular array, starting from an empty slot, which exists because $|S| < 2^b$. An update changes one run by one remainder, and the stated shift of the rest of its cluster restores the greedy placement; the metadata bits change only at the shifted slots and at the slot of $q(u)$.

## Depends on

- [Quotient filter](quotient-filter.md)

## Sources

- M. A. Bender, M. Farach-Colton, R. Johnson, R. Kraner, B. C. Kuszmaul, D. Medjedovic, P. Montes, P. Shetty, R. P. Spillane and E. Zadok, "Don't Thrash: How to Cache Your Hash on Flash", Proceedings of the VLDB Endowment 5(11), 2012 (Section 3).
- A. Pagh, R. Pagh and S. S. Rao, "An Optimal Bloom Filter Replacement", Proceedings of the 16th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2005.
