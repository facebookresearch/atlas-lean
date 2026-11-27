# Nonce-based counter mode is nonce CPA secure

Let $F$ be a PRF on blocks $\mathcal{N} \times \{0, \dots, \ell-1\}$ (nonce followed by a counter). Nonce-based CTR encrypts $m_1 \| \cdots \| m_\ell$ under nonce $N$ as $(m_j \oplus F(k, (N, j)))_j$. If $F$ is a PRF, nonce-based CTR is nonce CPA secure with advantage at most $2\,\mathrm{PRFadv}(F)$; there is no birthday term.

## Proof sketch

Distinct nonces give disjoint sets of PRF inputs, so with a random function every pad block is fresh and uniform.

## Depends on

- [Nonce-based symmetric encryption and nonce CPA security](nonce-based-encryption.md)
- [PRF advantage](../pseudorandom-functions/prf-advantage.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
