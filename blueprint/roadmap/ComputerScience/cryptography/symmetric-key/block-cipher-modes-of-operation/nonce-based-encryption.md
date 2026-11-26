# Nonce-based symmetric encryption and nonce CPA security

A *nonce-based cipher* encrypts as $c = E(k, m, N)$ deterministically given a nonce $N$ from a nonce space, and decrypts with the same nonce. It is *nonce CPA secure* if every efficient adversary that never repeats a nonce across its encryption queries has negligible advantage in the left-or-right experiment where each query $(m_0, m_1, N)$ with $|m_0| = |m_1|$ is answered by $E(k, m_b, N)$.

## Depends on

- [Private-key encryption scheme](../../security-games/generic-security-games/symm-enc-scheme.md)
- [CPA indistinguishability experiment](../../security-games/generic-security-games/cpa-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- P. Rogaway and T. Shrimpton, "A Provable-Security Treatment of the Key-Wrap Problem", Advances in Cryptology (EUROCRYPT 2006), LNCS 4004, 2006.
