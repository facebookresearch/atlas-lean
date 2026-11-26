# KEM–DEM hybrid encryption is CCA secure

If a KEM is CCA secure and a symmetric cipher (DEM) is one-time CCA secure (for example, one-time authenticated encryption), then the hybrid scheme encrypting $m$ as $(c_{\mathrm{kem}}, E_{\mathrm{sym}}(k, m))$ is a CCA-secure public-key scheme; the advantage is at most $2\,\mathrm{KEMadv} + \mathrm{DEMadv}$. Correctness of the hybrid follows from correctness of both parts.

## Proof sketch

Replace the encapsulated key by a uniform key, answering decapsulation of the challenge encapsulation with that uniform key; then the challenge is a one-time DEM challenge, and decryption queries with the challenge encapsulation become DEM decryption queries.

## Depends on

- [Hybrid encryption](../../key-encapsulation-and-hybrid-encryption/hybrid.md)
- [CPA experiment for key encapsulation](../../key-encapsulation-and-hybrid-encryption/kem-game.md)
- [Public-key CCA experiment](../../../security-games/generic-security-games/pub-cca-game.md)

## Proof depends on

- [Authenticated encryption implies chosen-ciphertext security](../../../symmetric-key/symmetric-encryption-security-notions/authenticated-encryption-implies-cca.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- R. Cramer and V. Shoup, "Design and Analysis of Practical Public-Key Encryption Schemes Secure against Adaptive Chosen Ciphertext Attack", SIAM Journal on Computing 33(1), 2003.
