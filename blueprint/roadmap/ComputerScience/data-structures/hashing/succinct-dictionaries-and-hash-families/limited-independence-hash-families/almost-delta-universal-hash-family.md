# Almost Δ-universal (difference-universal) hash families

Let $h : I \times X \to Y$ be a keyed hash family whose key $i$ is drawn from a probability distribution $\sigma$ on $I$, and let $Y$ be an additive group. The family is *$\varepsilon$-almost $\Delta$-universal* if for all distinct $x \ne x'$ in $X$ and every $d \in Y$,

$$
\Pr_{i \sim \sigma}\bigl[h_i(x) - h_i(x') = d\bigr] \le \varepsilon .
$$

When $Y = \{0,1\}^m$ with bitwise XOR this is $\varepsilon$-almost XOR-universal; with a uniform key it is an $\varepsilon$-bounded difference-unpredictable function. Taking $d = 0$ shows that an $\varepsilon$-almost $\Delta$-universal family is $\varepsilon$-universal, and the optimal value $\varepsilon = 1/|Y|$ is attained exactly when the difference $h_i(x) - h_i(x')$ is uniform on $Y$ for every pair of distinct inputs.

## Depends on

- [Bounded universal hash functions](../../../../cryptography/hash-functions/bounded-universal-hash-functions.md)

## Sources

- H. Krawczyk, "LFSR-based Hashing and Authentication", Advances in Cryptology (CRYPTO 1994), LNCS 839, 1994.
- P. Rogaway, "Bucket Hashing and Its Application to Fast Message Authentication", Advances in Cryptology (CRYPTO 1995), LNCS 963, 1995.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
- M. N. Wegman and J. L. Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences 22(3), 1981.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", CRC Press, 2020.
