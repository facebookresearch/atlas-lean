# One-way and unpredictable public-key encryption

A public-key scheme is *one-way* if every efficient adversary, given the public key and an encryption of a uniformly random message, outputs that message with negligible probability. It is *$\varepsilon$-unpredictable* if for every honest key pair, every message $m$ and every ciphertext $c$, $\Pr[E(pk, m) = c] \le \varepsilon$; equivalently, the scheme is $\gamma$-spread for $\varepsilon = 2^{-\gamma}$. It is *strongly unpredictable* if one negligible $\varepsilon(n)$ bounds $\Pr[E(pk, m) = c]$ for all public keys (including malformed or adversarial ones), messages and non-error ciphertexts.

## Depends on

- [Public-key encryption scheme](../../../security-games/generic-security-games/pkescheme.md)

## Sources

- E. Fujisaki and T. Okamoto, "Secure Integration of Asymmetric and Symmetric Encryption Schemes", Journal of Cryptology 26(1), 2013, Definitions 5.1 and 5.2.
- Dennis Hofheinz, Kathrin Hövelmanns and Eike Kiltz, "A Modular Analysis of the Fujisaki–Okamoto Transformation", Theory of Cryptography (TCC 2017), 2017.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023 (strong unpredictability).
