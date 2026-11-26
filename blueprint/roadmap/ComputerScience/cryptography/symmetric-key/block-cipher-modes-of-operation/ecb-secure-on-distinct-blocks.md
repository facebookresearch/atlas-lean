# ECB is one-time semantically secure on messages of distinct blocks

Let $E$ be a PRP and $\ell(n)$ a polynomial. Restricted to messages consisting of at most $\ell(n)$ pairwise distinct blocks (and challenge pairs of equal length), ECB mode is one-time semantically secure; the advantage is at most $2\,\mathrm{PRPadv}(E)$.

## Proof sketch

Replace $E(k,\cdot)$ by a random permutation. A random permutation maps distinct blocks to a uniformly random sequence of distinct blocks, independent of their values, so both challenge ciphertexts have the same distribution.

## Depends on

- [Electronic codebook (ECB) mode](ecb-mode.md)
- [Semantic security with error $\varepsilon$](../../security-games/semantic-security-and-indistinguishability/semantically-secure.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
