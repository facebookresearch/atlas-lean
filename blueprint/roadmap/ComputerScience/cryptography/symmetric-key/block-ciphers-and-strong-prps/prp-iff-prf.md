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

- M. Bellare and P. Rogaway, "The Security of Triple Encryption and a Framework for Code-Based Game-Playing Proofs", Advances in Cryptology (EUROCRYPT 2006), LNCS 4004, Springer, 2006, pp. 409–426, the PRP/PRF Switching Lemma, bound $q(q-1)/2^{n+1}$ (Lemma 1 of the full version).
- M. Bellare, J. Kilian and P. Rogaway, "The Security of the Cipher Block Chaining Message Authentication Code", Journal of Computer and System Sciences 61(3), 2000, pp. 362–399, Proposition 2.5 (PRF insecurity of a family of permutations is at most its PRP insecurity plus $q(q-1)/2^{l+1}$).
