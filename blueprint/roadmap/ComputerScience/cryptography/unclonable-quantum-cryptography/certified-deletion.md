# Encryption with certified deletion

A (public- or secret-key) encryption scheme with *certified deletion* has, in addition to encryption and decryption, an algorithm $\mathsf{Del}(\mathsf{ct})\to\mathsf{cert}$ that destroys a quantum ciphertext and outputs a classical certificate, and a verification $\mathsf{Vrfy}(\mathsf{vk},\mathsf{cert})$ using information kept by the encryptor. *Certified deletion security*: for any efficient adversary that receives an encryption of $m_b$, outputs a certificate and a residual state, the residual state is independent of $b$ (statistically close for both values of $b$) conditioned on the certificate being accepted, even if the adversary later learns the secret key (*everlasting* security against unbounded adversaries after deletion).

## Depends on

- [Indistinguishability of encryptions with error $\varepsilon$](../security-games/semantic-security-and-indistinguishability/ind-secure.md)
- [Wiesner's private-key quantum money](wiesner-quantum-money.md)

## Sources

- Anne Broadbent, Rabib Islam, "Quantum Encryption with Certified Deletion", TCC (2020).
- James Bartusek, Dakshita Khurana, "Cryptography with Certified Deletion", CRYPTO (2023), arXiv:2207.01754.
