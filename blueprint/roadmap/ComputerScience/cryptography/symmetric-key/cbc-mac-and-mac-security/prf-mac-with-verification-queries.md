# PRF-based MACs resist verification queries without a multiplicative loss

Let $F$ be a length-preserving keyed function on $n$-bit strings and let the MAC tag $m$ by $F(k, m)$. For every adversary making $Q_s$ signing and $Q_v$ verification queries, the winning probability in the game with verification queries is at most

$$\mathrm{PRFadv}(B) + \frac{Q_v}{2^n},$$

for a PRF distinguisher $B$ making at most $Q_s + Q_v$ queries; there is no factor $Q_v$ on the PRF advantage.

## Proof sketch

The distinguisher answers both kinds of queries using its oracle and outputs $1$ if some fresh verification query accepts. With a random function each fresh verification query accepts with probability $2^{-n}$.

## Depends on

- [MAC security with verification queries](mac-security-with-verification-queries.md)
- [PRF advantage](../pseudorandom-functions/prf-advantage.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
