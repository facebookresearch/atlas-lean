# Functional encryption and its semantic security

A *functional encryption* scheme for a functionality $F : \mathcal{K} \times M \to Y$ with a null identifier $\varepsilon$ consists of setup (producing a master public and secret key), key generation (a key $sk_\kappa$ for each $\kappa \in \mathcal{K}$), encryption, and deterministic decryption with $D(sk_\kappa, E(mpk, m)) = F(\kappa, m)$. In the semantic-security game the adversary gets $mpk$ and $sk_\varepsilon$, adaptively requests keys before and after one challenge pair $(m_0, m_1)$, and the experiment outputs $0$ unless $F(\kappa, m_0) = F(\kappa, m_1)$ for $\varepsilon$ and every queried $\kappa$.

## Depends on

- [Public-key encryption scheme](../../../security-games/generic-security-games/pkescheme.md)

## Sources

- D. Boneh, A. Sahai and B. Waters, "Functional Encryption: Definitions and Challenges", Theory of Cryptography (TCC 2011), LNCS 6597, 2011.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
