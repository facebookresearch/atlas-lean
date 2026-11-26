# Half-block encryption with a strong PRP is CCA secure

Let $E$ be a strong PRP on $2n$-bit blocks. The half-block cipher encrypts an $n$-bit message $m$ as $E(k, r \| m)$ for a fresh uniform $r \in \{0,1\}^n$, and decrypts $c$ to the last $n$ bits of $D(k, c)$ (rejecting words of other lengths). It is CCA secure.

## Proof sketch

Replace $E$ by a random permutation and then, with a table that answers redundant queries so that the permutation oracle receives none, by the forgetful two-sided oracle. Encryption outputs are then fresh uniform blocks independent of the message unless a nonce collides, and decryptions of non-challenge ciphertexts are independent of the challenge bit.

## Depends on

- [Strong pseudorandom permutation](../block-ciphers-and-strong-prps/strong-pseudorandom-permutation.md)
- [CCA indistinguishability experiment](../../security-games/generic-security-games/cca-game.md)

## Proof depends on

- [Two-sided switching lemma against the forgetful sampler](../block-ciphers-and-strong-prps/two-sided-switching-lemma.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- M. Bellare and P. Rogaway, "Encode-then-Encipher Encryption: How to Exploit Nonces or Redundancy in Plaintexts for Efficient Cryptography", Advances in Cryptology (ASIACRYPT 2000), LNCS 1976, 2000.
