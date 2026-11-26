# Perfectly secret ciphers have zero semantic-security advantage

Let a (possibly randomized) cipher with an arbitrary key distribution be perfectly secret: for all messages $m_0, m_1$ the ciphertext distributions $E(K, m_0)$ and $E(K, m_1)$ coincide. Then for every adversary, even computationally unbounded, and every admissibility predicate on challenge pairs, the one-time semantic-security advantage is $0$. This applies to the one-time pad and to the variable-length one-time pad on equal-length pairs.

## Proof sketch

The adversary's view in the experiment with bit $b$ is its state together with a sample of $E(K, m_b)$; these laws are equal for $b = 0, 1$.

## Depends on

- [Semantic security with error $\varepsilon$](../../security-games/semantic-security-and-indistinguishability/semantically-secure.md)
- [The group one-time pad is perfectly secret](../one-time-pad-over-a-finite-group/group-otp-perfectly-secret.md)

## Sources

- C. E. Shannon, "Communication Theory of Secrecy Systems", Bell System Technical Journal 28(4), 1949.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
