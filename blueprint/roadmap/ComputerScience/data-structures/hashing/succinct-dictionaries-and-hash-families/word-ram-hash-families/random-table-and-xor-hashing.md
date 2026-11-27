# Random-table and XOR-shift hashing

A *random table* hash on an index set $[2^M]$ is a table $Z$ of $2^M$ independent uniform $M$-bit words; it is fully independent on $[2^M]$. Composed with functions $f$ and $g$ of the key into $[2^M]$, fixed or chosen independently of $Z$, the *XOR-shifted* hash $u \mapsto f(u) \oplus Z[g(u)]$ is uniform for every key, and is pairwise independent on keys with distinct $g$-values. On the randomized Word RAM with $M < w$, filling $Z$ by uniform sampling (one `rand` draw below $2^M$ per entry) takes $O(2^M)$ instructions and $2^M$ random draws, and each evaluation takes $O(1)$ instructions.

## Depends on

- [k-wise independent hash family](k-wise-independent-hash-family.md)
- [Simple tabulation hashing](simple-tabulation-hashing.md)

## Proof depends on

- [Exact uniform resampling of random tables on the Word RAM](exact-uniform-table-resampling.md)

## Sources

- J. L. Carter and M. N. Wegman, "Universal Classes of Hash Functions", Journal of Computer and System Sciences 18(2), 1979.
- M. Mitzenmacher and E. Upfal, "Probability and Computing", 2nd edition, Cambridge University Press, 2017.
