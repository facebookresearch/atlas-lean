# From per-operation to per-sequence high-probability bounds

If a with-high-probability Word-RAM implementation executes each operation within a worst-case budget $B$ except with probability at most $\delta$ (against operation sequences fixed in advance), then on every such sequence of $m$ operations all operations finish within $B$ instructions with probability at least $1 - m \delta$, and the expected number of operations exceeding $B$ is at most $m\delta$. In particular, with $\delta = n^{-c}$ and $m \le n^{c'}$ for $c' < c$, every operation is fast with probability $1 - n^{c' - c}$.

## Proof sketch

Union bound over the $m$ operations, and linearity of expectation for the count of slow operations.

## Depends on

- [Word-RAM implementation certificate with potential-amortized running time](word-ram-implementation-certificate.md)

## Sources

- M. Mitzenmacher and E. Upfal, "Probability and Computing", 2nd edition, Cambridge University Press, 2017.
- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
