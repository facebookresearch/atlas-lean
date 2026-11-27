# Output feedback (OFB) mode is CPA secure

For a PRF $F$ on $b$-bit blocks, OFB mode encrypts $m_1 \| \cdots \| m_\ell$ by choosing a uniform $x_0$, setting $x_i = F(k, x_{i-1})$ and outputting $x_0 \| (m_1 \oplus x_1) \| \cdots \| (m_\ell \oplus x_\ell)$. If $F$ is a PRF and $2^{-b}$ is negligible, OFB mode is CPA secure, with advantage at most $2\,\mathrm{PRFadv}(F) + (Q\ell)^2/2^b$ for an adversary making $Q$ queries of at most $\ell$ blocks.

## Proof sketch

With a random function the chain values are fresh uniform blocks until some chain value repeats an earlier input, a birthday event over the $Q\ell$ chain values.

## Depends on

- [PRF advantage](../pseudorandom-functions/prf-advantage.md)
- [CPA indistinguishability experiment](../../security-games/generic-security-games/cpa-game.md)

## Proof depends on

- [Fundamental lemma of game playing for stateful oracle handlers](../../security-games/identical-until-bad-oracle-handlers/fundamental-lemma-for-stateful-handlers.md)
- [Triangular (birthday-type) bound for linearly growing bad sets](../../security-games/identical-until-bad-oracle-handlers/triangular-bad-event-bound.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
