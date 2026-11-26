# The one-block PRF cipher is not CCA secure

The cipher $m \mapsto r \,\|\, (F(k, r) \oplus m)$ (uniform $r$, $n$-bit messages) is CPA secure when $F$ is a PRF, but it is not CCA secure: the adversary chooses $m_0 = 0^n$ and $m_1 = 1^n$, and given a challenge ciphertext $r \| c$ it flips the first bit of $c$ and asks for the decryption of the resulting ciphertext, which differs from the challenge; the answer is $10^{n-1}$ if $b = 0$ and $01^{n-1}$ if $b = 1$, so the adversary always outputs the correct bit.

## Proof sketch

The modified ciphertext decrypts to $F(k,r) \oplus c \oplus 10^{n-1} = m_b \oplus 10^{n-1}$.

## Depends on

- [CCA indistinguishability experiment](../../security-games/generic-security-games/cca-game.md)
- [Encryption from a keyed function](../pseudorandom-functions/encrypt.md)

## Proof depends on

- [Malleability of random-IV stream encryption](../block-cipher-modes-of-operation/random-iv-stream-encryption-malleability.md)

## Sources

- Jonathan Katz and Yehuda Lindell, "Introduction to Modern Cryptography", 3rd ed., CRC Press, 2020, Construction 3.28, Theorem 3.29 and Section 5.1.
