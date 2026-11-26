# Counter-stateful MACs from nonce-based MACs

Let a nonce-based MAC be secure against adversaries that never repeat a nonce in signing queries. The stateful MAC that keeps a counter $i$, tags the $i$-th message $m$ as $(i, S(k, m, i))$ and increments $i$, and verifies $(i, t)$ by $V(k, m, t, i)$, is a secure (stateful) MAC.

## Proof sketch

The counter never repeats, so the signing queries of the stateful scheme are nonce-respecting queries of the nonce-based scheme, and a forgery for the stateful scheme is one for the nonce-based scheme.

## Depends on

- [Message authentication code](../../security-games/generic-security-games/macscheme.md)
- [MAC forgery experiment](../../security-games/generic-security-games/mac-game.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
