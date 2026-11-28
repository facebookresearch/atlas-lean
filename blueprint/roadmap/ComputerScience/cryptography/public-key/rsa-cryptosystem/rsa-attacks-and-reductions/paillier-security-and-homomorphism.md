# Paillier encryption is IND-CPA under DCR, additively homomorphic, and not CCA secure

(a) Paillier encryption is correct and semantically secure under the DCR assumption. (b) It is additively homomorphic: the product of encryptions of $m_1$ and $m_2$ modulo $N^2$ is an encryption of $m_1 + m_2 \bmod N$, and multiplying by a fresh encryption of $0$ makes it statistically indistinguishable from a fresh encryption. (c) Consequently it is not CCA secure.

## Proof sketch

(a) Under DCR, $r^N$ can be replaced by a uniform unit of $\mathbb{Z}_{N^2}^*$, which makes $(1+N)^m r^N$ uniform independently of $m$. (b) $(1+N)^{m_1} r_1^N (1+N)^{m_2} r_2^N = (1+N)^{m_1+m_2}(r_1r_2)^N$. (c) Maul the challenge by multiplying with an encryption of $1$ and ask for its decryption.

## Depends on

- [Paillier encryption](paillier-encryption.md)
- [Public-key eavesdropping experiment](../../../security-games/generic-security-games/pub-cpa-game.md)
- [Homomorphic encryption: correctness and compactness](../../homomorphic-encryption/homomorphic-encryption-correctness-and.md)

## Sources

- P. Paillier, "Public-Key Cryptosystems Based on Composite Degree Residuosity Classes", Advances in Cryptology (EUROCRYPT 1999), LNCS 1592, 1999.
- J. Katz and Y. Lindell, "Introduction to Modern Cryptography", 3rd edition, CRC Press, 2020.
