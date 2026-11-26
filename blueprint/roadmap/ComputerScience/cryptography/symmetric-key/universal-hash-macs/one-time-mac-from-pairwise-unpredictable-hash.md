# One-time MACs from pairwise-unpredictable hashing

Let $H$ be $\varepsilon$-pairwise unpredictable with a uniform private key. The MAC that tags $m$ by $H(k, m)$ and verifies by equality is a *one-time MAC*: every forger that makes at most one tagging query and outputs a fresh valid pair $(m^*, t^*)$ with $m^*$ different from the queried message succeeds with probability at most $\varepsilon$. (A valid pair with the queried message would repeat the correct tag, so a forgery yields a prediction of the hash of a distinct message.)

## Proof sketch

Conditioned on the answer $y_0 = H(k, m_0)$ to the query, the forgery is correct with probability $\Pr[H(k, m^*) = t^* \mid H(k, m_0) = y_0] \le \varepsilon$; average over the forger's choices.

## Depends on

- [$\varepsilon$-almost-$\Delta$-universal and pairwise-unpredictable hash families](delta-universal-hash-families.md)
- [The MAC forgery experiment](../pseudorandom-functions/mac-game.md)

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
