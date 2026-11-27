# Pairwise unpredictability implies universality and difference universality

Let $H : K \times M \to T$ be a keyed hash with a finite uniform private key. In the pairwise-unpredictability game the adversary chooses $m_0$, receives $H(k, m_0)$, keeps arbitrary private state, and outputs $m_1 \ne m_0$ and a guess $t_1$; it wins if $H(k, m_1) = t_1$. Suppose every adversary wins with probability at most $\varepsilon$ ($H$ is an $\varepsilon$-PUF). Then $H$ is $\varepsilon$-universal: $\Pr_k[H(k,m) = H(k,m')] \le \varepsilon$ for all $m \ne m'$. If moreover $T$ is an additive group, then $H$ is $\varepsilon$-almost $\Delta$-universal: $\Pr_k[H(k,m) - H(k,m') = d] \le \varepsilon$ for all $m \ne m'$ and $d \in T$.

## Proof sketch

Given $m \ne m'$ and $d$, the adversary queries $m'$, receives $t = H(k, m')$ and outputs $(m, t + d)$; it wins exactly when $H(k,m) - H(k,m') = d$. Taking $d = 0$ gives universality.

## Depends on

- [Almost Δ-universal (difference-universal) hash families](../../../data-structures/hashing/succinct-dictionaries-and-hash-families/limited-independence-hash-families/almost-delta-universal-hash-family.md)
- [Carter–Wegman MACs](../../symmetric-key/macs-and-modes/carterwegman-macs.md)
- [Bounded universal hash functions](../bounded-universal-hash-functions.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", version 0.6, 2023.
