# Projective hash games against unbounded adaptive adversaries

Against computationally unbounded adaptive adversaries that may make hash-evaluation queries on Diffie–Hellman pairs: (a) for any pair $(v, w)$ off the Diffie–Hellman pairs chosen by the adversary, the value $z$ is distributed uniformly given the projection and all answers, so the real and random-$z$ experiments have identical output distributions; (b) in the universal$_2$ game, after seeing one tagged value on a non-DH pair, the adversary predicts the tagged value on another non-DH pair with a different tag in any of $Q$ guesses with probability at most $Q/q$.

## Proof sketch

Evaluation queries on Diffie–Hellman pairs are determined by the projection, so they leak nothing beyond it; the claims then follow from universality and its tagged version.

## Depends on

- [Diffie–Hellman projective hash function](diffie-hellman-projective-hash.md)

## Proof depends on

- [Universality of the projective hash off Diffie–Hellman pairs](projective-hash-universality.md)

## Sources

- R. Cramer and V. Shoup, "Design and Analysis of Practical Public-Key Encryption Schemes Secure against Adaptive Chosen Ciphertext Attack", SIAM Journal on Computing 33(1), 2003.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
