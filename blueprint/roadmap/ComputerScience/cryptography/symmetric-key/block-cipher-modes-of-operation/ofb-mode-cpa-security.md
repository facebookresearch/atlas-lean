# Output feedback (OFB) mode is CPA secure

For a PRF $F$ on $b$-bit blocks, OFB mode encrypts $m_1 \| \cdots \| m_\ell$ by choosing a uniform $x_0$, setting $x_i = F(k, x_{i-1})$ and outputting $x_0 \| (m_1 \oplus x_1) \| \cdots \| (m_\ell \oplus x_\ell)$. If $\ell$ is poly-bounded, $F$ is a secure PRF and $2^{-b}$ is negligible, OFB mode is CPA secure.

## Proof sketch

Replace $F(k, \cdot)$ by a random function in each of the two CPA experiments, at a cost of $\mathrm{PRFadv}(F)$ each. With a random function the chain values are fresh uniform blocks, independent of the messages, until some chain value repeats an earlier input of the function, a birthday event over the at most $Q\ell$ inputs of an adversary making $Q$ queries of at most $\ell$ blocks, of probability at most $(Q\ell)^2/2^{b+1}$ in each experiment. The CPA advantage is therefore at most $2\,\mathrm{PRFadv}(F) + (Q\ell)^2/2^b$, which is negligible.

## Depends on

- [PRF advantage](../pseudorandom-functions/prf-advantage.md)
- [CPA indistinguishability experiment](../../security-games/generic-security-games/cpa-game.md)

## Proof depends on

- [Fundamental lemma of game playing for stateful oracle handlers](../../security-games/identical-until-bad-oracle-handlers/fundamental-lemma-for-stateful-handlers.md)
- [Triangular (birthday-type) bound for linearly growing bad sets](../../security-games/identical-until-bad-oracle-handlers/triangular-bad-event-bound.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023, Exercise 5.15(b) (OFB mode over $\{0,1\}^n$ is CPA secure when $F$ is a secure PRF and $|\mathcal{X}|$ is super-poly).
