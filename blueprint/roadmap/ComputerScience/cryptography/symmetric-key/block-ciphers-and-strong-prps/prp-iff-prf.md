# A block cipher with super-polynomial block space is a PRP iff it is a PRF

Let $E$ be a block cipher with block length $b(n)$ such that $2^{-b(n)}$ is negligible. Then $E$ is a pseudorandom permutation if and only if it is a pseudorandom function (viewed as a keyed function $\{0,1\}^{b(n)} \to \{0,1\}^{b(n)}$), against efficient adaptive adversaries. For a $Q$-query adversary the PRP and PRF advantages differ by at most $\binom{Q}{2}/2^{b(n)}$.

## Proof sketch

Both directions follow from the PRP/PRF switching lemma: the ideal permutation and the ideal function are distinguishable with advantage at most $\binom{Q}{2}/2^{b}$, and the real experiments coincide.

## Depends on

- [Block cipher (uniform family)](block-cipher.md)
- [Asymptotic PRF security relative to a class of distinguishers](../pseudorandom-functions/prfsecure.md)

## Proof depends on

- [Switching lemma with the birthday bound](../../security-games/lazy-sampling-and-the-prp-prf-switching-lemma/switching-lemma-le.md)
- [A PRP family is a PRF family](../pseudorandom-permutations/prf-secure-of-prp-secure.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
