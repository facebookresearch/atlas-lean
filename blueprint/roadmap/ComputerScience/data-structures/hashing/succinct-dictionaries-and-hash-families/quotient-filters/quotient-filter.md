# Quotient filter

A *quotient filter* with $2^b$ slots and $f$-bit remainders stores a set $S$ by hashing each key $u$ to a fingerprint split into a quotient $q(u) \in [2^b]$ and a remainder $r(u) \in [2^f]$. The sorted remainders of the keys with quotient $q$ form the *run* of bucket $q$. Runs are stored in increasing order of quotient in a circular array of slots, each run starting at slot $q$ or after the preceding runs when those overflow; each slot carries three metadata bits: *occupied* (some key has this slot's index as quotient), *continuation* or *run-start* (this slot begins a run), and *shifted* or *full* (the slot holds a remainder). A maximal sequence of full slots is a *cluster*. A query for $u$ reports yes iff $r(u)$ occurs in the run of $q(u)$.

## Depends on

- [Dynamic approximate-membership filter](dynamic-approximate-membership-filter.md)

## Sources

- A. Pagh, R. Pagh and S. S. Rao, "An Optimal Bloom Filter Replacement", Proceedings of the 16th ACM-SIAM Symposium on Discrete Algorithms (SODA), 2005.
- M. A. Bender, M. Farach-Colton, R. Johnson, R. Kraner, B. C. Kuszmaul, D. Medjedovic, P. Montes, P. Shetty, R. P. Spillane and E. Zadok, "Don't Thrash: How to Cache Your Hash on Flash", Proceedings of the VLDB Endowment 5(11), 2012.
