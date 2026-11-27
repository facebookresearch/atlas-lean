# IND-CPA-D security for approximate homomorphic encryption

For a (possibly approximate) homomorphic encryption scheme, the *IND-CPA-D* game gives the adversary, besides the public and evaluation keys, an encryption oracle on pairs $(m_0,m_1)$ returning an encryption of $m_b$, an evaluation oracle applying a circuit $f$ to stored ciphertexts, and a decryption oracle that returns the decryption of a stored ciphertext only if its two shadow plaintexts (computed on $m_0$-inputs and $m_1$-inputs) agree, i.e., $f(\mathbf{m}_0)=f(\mathbf{m}_1)$. The scheme is IND-CPA-D secure if no efficient adversary guesses $b$ with non-negligible advantage. For exact schemes whose decryption is correct with overwhelming probability on every evaluated circuit, IND-CPA-D is equivalent to IND-CPA, but for approximate schemes decryptions reveal the error.

## Depends on

- [Indistinguishability of encryptions with error $\varepsilon$](../../../security-games/semantic-security-and-indistinguishability/ind-secure.md)
- [CKKS ciphertexts and approximate decryption](ckks-ciphertexts.md)

## Sources

- Baiyu Li, Daniele Micciancio, "On the Security of Homomorphic Encryption on Approximate Numbers", EUROCRYPT (2021), IACR ePrint 2020/1533.
