# One-way and unpredictable public-key encryption

A public-key scheme is *one-way* if every efficient adversary, given the public key and an encryption of a uniformly random message, outputs that message with negligible probability. It is *$\varepsilon$-unpredictable* if for every honest key pair, every message $m$ and every ciphertext $c$, $\Pr[E(pk, m) = c] \le \varepsilon$; it is *strongly unpredictable* if one negligible $\varepsilon(n)$ bounds $\Pr[E(pk, m) = c]$ for all public keys (including malformed or adversarial ones), messages and non-error ciphertexts.

## Depends on

- [Public-key encryption scheme](../../../security-games/generic-security-games/pkescheme.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
