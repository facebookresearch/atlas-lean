# One-time MACs from pairwise-unpredictable hashing

Let $H$ be $\varepsilon$-pairwise unpredictable with a uniform private key. The MAC that tags $m$ by $H(k, m)$ and verifies by equality is a *one-time MAC*: every forger that makes at most one tagging query and outputs a fresh valid pair $(m^*, t^*)$ with $m^*$ different from the queried message succeeds with probability at most $\varepsilon$. (A valid pair with the queried message would repeat the correct tag, so a forgery yields a prediction of the hash of a distinct message.)

## Proof sketch

Conditioned on the answer $y_0 = H(k, m_0)$ to the query, the forgery is correct with probability $\Pr[H(k, m^*) = t^* \mid H(k, m_0) = y_0] \le \varepsilon$; average over the forger's choices.

## Depends on

- [$\varepsilon$-almost-$\Delta$-universal and pairwise-unpredictable hash families](delta-universal-hash-families.md)
- [The MAC forgery experiment](../pseudorandom-functions/mac-game.md)

## Sources

- Mark N. Wegman and J. Lawrence Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences 22(3), 1981, pp. 265–279, Sections 2 and 3 (an authentication system is unbreakable with certainty $p$ if, after seeing the tag of any message, possibly chosen by the forger, the forger guesses the tag of a different message with probability at most $p$; this holds when, among the keys consistent with the observed pair, the fraction mapping any other message to any given tag is at most $p$: $1/|T|$ for strongly universal$_2$ classes and $2/|B'|$ for their almost strongly universal$_2$ class).
