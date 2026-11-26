# Random-table and XOR-shift hashing

A *random table* hash on an index set $[2^M]$ is a table $Z$ of $2^M$ independent uniform $M$-bit words; it is fully independent on $[2^M]$. Composed with functions $f, g$ of the key, the *XOR-shifted* hash $u \mapsto f(u) \oplus Z[g(u)]$ is uniform for every key, and is pairwise independent on keys with distinct $g$-values. On the Word RAM, filling $Z$ by uniform word sampling takes $O(2^M)$ instructions and $2^M$ random draws, and each evaluation takes $O(1)$ instructions.

## Depends on

- [k-wise independent hash family](k-wise-independent-hash-family.md)
- [Simple tabulation hashing](simple-tabulation-hashing.md)

## Sources

- J. L. Carter and M. N. Wegman, "Universal Classes of Hash Functions", Journal of Computer and System Sciences 18(2), 1979.
- M. Mitzenmacher and E. Upfal, "Probability and Computing", 2nd edition, Cambridge University Press, 2017.
