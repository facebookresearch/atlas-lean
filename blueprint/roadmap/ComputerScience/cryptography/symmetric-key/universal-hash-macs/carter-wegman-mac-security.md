# One-time and multi-query security of Carter–Wegman MACs

Let $H$ be $\varepsilon$-AXU into a finite abelian group $Y$. The one-time Carter–Wegman MAC tags $m$ with $H(k, m) + r$ for a uniform private pad $r \in Y$. (i) Without any tagging query, every forgery succeeds with probability exactly $1/|Y|$, for every hash family. (ii) After one adaptive tagging query, every forger succeeds in existential (and in strong) forgery with probability at most $\varepsilon$. (iii) With an independent fresh pad for each issued counter value (pads indexed by a counter or slot), every forger making $Q$ tagging queries succeeds with probability at most $\varepsilon$ per forgery attempt, i.e. at most $\varepsilon$ for existential forgery and at most $\max(\varepsilon, 1/|Y|)$ for strong forgery at a fresh slot.

## Proof sketch

With pad $r$ uniform, a single tag is uniform and independent of $k$. A forgery $(m^*, t^*)$ for the queried slot is valid iff $H(k, m^*) - H(k, m) = t^* - t$, which has probability at most $\varepsilon$ over $k$ given the tag; at an unused slot the pad makes the tag uniform.

## Depends on

- [$\varepsilon$-almost-$\Delta$-universal and pairwise-unpredictable hash families](delta-universal-hash-families.md)
- [The MAC forgery experiment](../pseudorandom-functions/mac-game.md)

## Sources

- Mark N. Wegman and J. Lawrence Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences, 1981.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
