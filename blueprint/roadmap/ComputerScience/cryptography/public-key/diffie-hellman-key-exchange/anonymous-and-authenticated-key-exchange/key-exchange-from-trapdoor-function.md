# Key exchange from a trapdoor function

Let $(G, F, I)$ be a trapdoor function scheme (key generation producing $(pk, sk)$, evaluation $F(pk, \cdot)$, inversion $I(sk, \cdot)$). The protocol in which Alice sends $pk$, Bob sends $y = F(pk, x)$ for a uniform $x$, and both output $x$ (Alice via $I(sk, y)$) is correct and key-guessing secure if and only if the trapdoor function is one-way. Instantiating with RSA gives RSA key exchange.

## Proof sketch

The transcript $(pk, F(pk, x))$ is exactly a one-wayness challenge and the key is its preimage.

## Depends on

- [Key-guessing security of anonymous key exchange](key-guessing-security-of-key-exchange.md)
- [Trapdoor permutations](../../hardness-assumptions/trapdoor-permutations.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
