# An ignored ciphertext bit breaks CCA security

Let $(G, E, D)$ be any public-key scheme and define $E'(pk, m) = E(pk, m) \| 0$ with $D'(sk, c\|b) = D(sk, c)$, ignoring the last bit. Then $E'$ is CPA secure whenever $E$ is, but $E'$ is not CCA secure: flipping the last bit of the challenge gives a different ciphertext that decrypts to $m_b$.

## Proof sketch

CPA security transfers directly; the CCA adversary queries $c^* \oplus 0\cdots01$.

## Depends on

- [1CCA security of public-key encryption](one-cca-security.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
