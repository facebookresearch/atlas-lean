# Predicting a hidden bit from a distinguishing test

Let $(Z, b)$ be a jointly distributed pair of a string $Z$ and a bit $b$, and let $D$ be a test with

$$\Pr[D(Z, b) = 1] - \Pr[D(Z, r) = 1] = \varepsilon,$$

where $r$ is a uniform bit independent of $(Z, b)$. The predictor $P$ that draws a uniform bit $r$, runs $D(Z, r)$, and outputs $r$ if $D$ accepts and $1 - r$ otherwise satisfies $\Pr[P(Z) = b] = \tfrac{1}{2} + \varepsilon$. Conversely, any predictor with success $\tfrac{1}{2} + \varepsilon$ gives the test "accept iff $P(Z)$ equals the given bit" with distinguishing gap exactly $\varepsilon$.

## Proof sketch

Condition on whether $r = b$; when $r = b$ the predictor is correct iff $D$ accepts, and when $r \ne b$ it is correct iff $D$ rejects. Expanding $\Pr[D(Z,r)=1]$ as the average of the two conditional acceptance probabilities gives the identity.

## Depends on

- [Distinguishing advantage](../games-and-advantages/advantage.md)
- [Guessing advantage](../games-and-advantages/guess-advantage.md)

## Sources

- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
