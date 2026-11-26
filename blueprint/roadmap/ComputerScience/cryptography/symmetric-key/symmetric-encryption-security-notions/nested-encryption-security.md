# Nested encryption is secure when all but one key is revealed

Let $E$ be a one-time semantically secure cipher whose ciphertexts lie in its message space, so that the $t$-fold nested cipher $E_t((k_1, \dots, k_t), m) = E(k_t, \cdots E(k_1, m))$ is defined. Assume $E$ *preserves admissibility*: encryptions of an admissible challenge pair under the same key form an admissible pair (true for the equal-length rule when ciphertext length is determined by message length). Then $E_t$ remains semantically secure even if the adversary learns all keys except one, chosen arbitrarily. Without the admissibility-preservation hypothesis the claim fails: there are one-time perfectly secure ciphers whose two-layer nesting has advantage $1$.

## Proof sketch

If key $k_i$ is hidden, the reduction applies layers $1, \dots, i-1$ to both challenge messages with the known keys, submits the resulting pair as its challenge, and applies the remaining layers to the answer; admissibility preservation ensures the submitted pair is legal.

## Depends on

- [Semantic security with error $\varepsilon$](../../security-games/semantic-security-and-indistinguishability/semantically-secure.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
