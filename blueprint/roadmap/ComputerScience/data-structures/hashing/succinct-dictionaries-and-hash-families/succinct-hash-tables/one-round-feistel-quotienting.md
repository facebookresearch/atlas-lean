# One-round Feistel quotienting of keys

Let $U$ be a universe of keys of $\kappa = \lceil \log_2 U \rceil$ bits and $b \le \kappa$. Split a key $u$ into its low part $u_{\mathrm{lo}} = u \bmod 2^b$ and its quotient $u_{\mathrm{hi}} = \lfloor u / 2^b \rfloor$, of $\kappa - b$ bits. Given a hash function $h$ on quotients, the *Feistel bucket* of $u$ is

$$
\beta(u) = \left(h(u_{\mathrm{hi}}) \bmod 2^b\right) \oplus u_{\mathrm{lo}} \in [2^b].
$$

A table with $2^b$ buckets stores in bucket $\beta(u)$ only the quotient $u_{\mathrm{hi}}$ (and the value), saving $b$ bits per key. The map $u \mapsto (\beta(u), u_{\mathrm{hi}})$ is a bijection, since $u_{\mathrm{lo}} = \beta(u) \oplus (h(u_{\mathrm{hi}}) \bmod 2^b)$ recovers the key.

## Depends on

- [Luby–Rackoff theorem](../../../../cryptography/symmetric-key/pseudorandom-constructions/lubyrackoff-theorem.md)

## Sources

- Y. Arbitman, M. Naor and G. Segev, "Backyard Cuckoo Hashing: Constant Worst-Case Operations with a Succinct Representation", Proceedings of the 51st IEEE Symposium on Foundations of Computer Science (FOCS), 2010.
- M. A. Bender, A. Conway, M. Farach-Colton, W. Kuszmaul and G. Tagliavini, "Iceberg Hashing: Optimizing Many Hash-Table Criteria at Once", Journal of the ACM 70(6), 2023.
- M. Luby and C. Rackoff, "How to Construct Pseudorandom Permutations from Pseudorandom Functions", SIAM Journal on Computing 17(2), 1988.
