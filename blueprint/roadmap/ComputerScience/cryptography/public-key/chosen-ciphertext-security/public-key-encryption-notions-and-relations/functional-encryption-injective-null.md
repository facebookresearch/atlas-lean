# Functional encryption with an injective null function has zero advantage

If the null function $F(\varepsilon, \cdot)$ is injective, then every functional encryption scheme for $F$, including the trivial scheme that publishes the message, has semantic-security advantage $0$ against every adversary, because only pairs with $m_0 = m_1$ are admissible. A public-key scheme viewed as functional encryption for the identity with null function $m \mapsto |m|$ is correct exactly when the scheme is correct and the public null key computes the message length.

## Proof sketch

Admissibility forces $F(\varepsilon, m_0) = F(\varepsilon, m_1)$, hence $m_0 = m_1$, so the two experiments coincide. The correctness characterization unfolds the definitions.

## Depends on

- [Functional encryption and its semantic security](functional-encryption.md)

## Sources

- D. Boneh, A. Sahai and B. Waters, "Functional Encryption: Definitions and Challenges", Theory of Cryptography (TCC 2011), LNCS 6597, 2011.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
