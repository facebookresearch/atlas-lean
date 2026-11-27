# Computing small string attractors is NP-complete

For every $k \ge 3$, constant or not, the *$k$-attractor problem*, deciding for a string $T$ and an integer $t$ whether there is a set of $t$ positions crossed by some occurrence of every substring of length at most $k$, is NP-complete. Consequently computing $\gamma(T)$ is NP-hard.

## Proof sketch

Membership in NP is clear since a candidate set can be verified in polynomial time. For hardness, Kempa and Prezza reduce from $k$-Set Cover, which is NP-complete for every constant $k \ge 3$: from a universe of size $u$ and sets $C_1, \dots, C_m$ of sizes $n_i \le k$ they build, over gadget letters and delimiters, a string $T_C$ of length $O(uk^2 + tk + t')$ with $t = \sum_i n_i$ and $t' = \sum_i n_i^2$, such that a cover of size at most $p$ exists if and only if $T_C$ has a $k$-attractor of size at most $4u(k-1) + p + 6t - 3m$. For $T_C$ the smallest $k$-attractor has the same size as the smallest $k'$-attractor for every $k \le k' \le |T_C|$, which extends hardness to non-constant $k$, in particular to $k = n$, i.e. to string attractors themselves. The problem is moreover APX-complete for constant $k \ge 3$.

## Depends on

- [String attractors](string-attractor.md)

## Sources

- Dominik Kempa, Nicola Prezza, "At the Roots of Dictionary Compression: String Attractors", STOC (2018), arXiv:1710.10964.
