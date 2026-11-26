# The one-block PRF cipher is not CCA secure

The cipher $m \mapsto r \,\|\, (F(k, r) \oplus m)$ (uniform $r$, $n$-bit messages) is CPA secure when $F$ is a PRF, but it is not CCA secure: given a challenge ciphertext $r \| c$, the adversary decrypts $r \| (c \oplus 1^n)$, which is a different ciphertext, and recovers $m_b \oplus 1^n$, obtaining advantage $1$.

## Proof sketch

The modified ciphertext decrypts to $F(k,r) \oplus c \oplus 1^n = m_b \oplus 1^n$.

## Depends on

- [CCA indistinguishability experiment](../../security-games/generic-security-games/cca-game.md)
- [Encryption from a keyed function](../pseudorandom-functions/encrypt.md)

## Proof depends on

- [Malleability of random-IV stream encryption](../block-cipher-modes-of-operation/random-iv-stream-encryption-malleability.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
