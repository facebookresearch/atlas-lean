# Quotient filter

A *quotient filter* with $2^b$ slots and $f$-bit remainders stores a set $S$ by hashing each key $u$ to a fingerprint split into a quotient $q(u) \in [2^b]$ and a remainder $r(u) \in [2^f]$; the multiset of fingerprints is stored, so the full fingerprint $(q(u), r(u))$ is recoverable. The remainders of the keys with quotient $q$ form the *run* of bucket $q$, stored in contiguous slots and here kept in sorted order. Runs are stored in increasing order of quotient in a circular array of slots, the run of $q$ starting at slot $q$ or, if that slot is taken by earlier runs, at the first slot after them (linear probing). Each slot holds an $f$-bit remainder and three metadata bits: *is-occupied* (some stored key has this slot's index as quotient), *is-continuation* (the remainder in this slot belongs to the same run as the remainder in the preceding slot) and *is-shifted* (the remainder in this slot is not in its home slot, that is, its quotient differs from the slot index). A *cluster* is a maximal sequence of consecutive nonempty slots; it consists of whole runs, is preceded by an empty slot and starts with an unshifted remainder. A query for $u$ reports yes iff $r(u)$ occurs in the run of $q(u)$.

## Depends on

- [Dynamic approximate-membership filter](dynamic-approximate-membership-filter.md)

## Sources

- M. A. Bender, M. Farach-Colton, R. Johnson, R. Kraner, B. C. Kuszmaul, D. Medjedovic, P. Montes, P. Shetty, R. P. Spillane and E. Zadok, "Don't Thrash: How to Cache Your Hash on Flash", Proceedings of the VLDB Endowment 5(11), 2012 (Section 3).
- A. Pagh, R. Pagh and S. S. Rao, "An Optimal Bloom Filter Replacement", Proceedings of the 16th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2005.
