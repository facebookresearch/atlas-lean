# BLS signatures

Let $e : G_1 \times G_2 \to G_T$ be a bilinear pairing on groups of prime order $q$ with generators $g_1, g_2$, and $H$ a hash onto $G_1$ (a random oracle). The *BLS signature* scheme has secret key $\alpha \in \mathbb{Z}_q$, public key $u = g_2^{\alpha}$, signs $m$ as $\sigma = H(m)^{\alpha}$, and accepts iff $e(\sigma, g_2) = e(H(m), u)$. Signatures aggregate by multiplication.

## Depends on

- [Bilinear groups](../../advanced-encryption-and-pairings/bilinear-groups.md)
- [Signature scheme](../../../security-games/generic-security-games/sig-scheme.md)
- [The random oracle model](../../random-oracle-constructions/the-random-oracle-model.md)

## Sources

- D. Boneh, B. Lynn and H. Shacham, "Short Signatures from the Weil Pairing", Journal of Cryptology 17(4), 2004.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
