# Multiplicative homomorphism of ElGamal

For ElGamal under public key $u$, componentwise multiplication of an encryption of $m_1$ with randomness $\beta_1$ and an encryption of $m_2$ with randomness $\beta_2$ yields the encryption of $m_1 m_2$ with randomness $\beta_1 + \beta_2$. Hence for every honest key pair and honest ciphertexts $c_1, c_2$, the product $c_1 \cdot c_2$ (computable in polynomial time from the ciphertexts alone) decrypts to $m_1 m_2$; multiplying by a fresh encryption of $1$ rerandomizes it.

## Proof sketch

$(g^{\beta_1} g^{\beta_2}, u^{\beta_1}m_1 u^{\beta_2}m_2) = (g^{\beta_1+\beta_2}, u^{\beta_1+\beta_2} m_1 m_2)$.

## Depends on

- [ElGamal encryption](../encrypt.md)
- [Homomorphic encryption: correctness and compactness](../../homomorphic-encryption/homomorphic-encryption-correctness-and.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- T. ElGamal, "A Public Key Cryptosystem and a Signature Scheme Based on Discrete Logarithms", IEEE Transactions on Information Theory 31(4), 1985.
