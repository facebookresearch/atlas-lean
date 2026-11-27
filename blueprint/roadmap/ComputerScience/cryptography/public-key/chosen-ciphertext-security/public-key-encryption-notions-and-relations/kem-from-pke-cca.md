# CCA-secure key encapsulation from CCA-secure public-key encryption

Let $(G, E, D)$ be a CCA-secure public-key scheme with message space containing $\{0,1\}^{\ell}$. The KEM that encapsulates by choosing a uniform key $k \in \{0,1\}^\ell$ and outputting $(k, E(pk, k))$, and decapsulates with $D$, is a CCA-secure KEM, with advantage at most twice the CCA advantage of a reduction.

## Proof sketch

The reduction submits two independent uniform keys $(k_0, k_1)$ as its challenge pair and gives $k_0$ to the KEM adversary as the candidate key; decapsulation queries are forwarded to the decryption oracle.

## Depends on

- [Key-encapsulation mechanism](../../key-encapsulation-and-hybrid-encryption/kemscheme.md)
- [CPA experiment for key encapsulation](../../key-encapsulation-and-hybrid-encryption/kem-game.md)
- [Public-key CCA experiment](../../../security-games/generic-security-games/pub-cca-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
