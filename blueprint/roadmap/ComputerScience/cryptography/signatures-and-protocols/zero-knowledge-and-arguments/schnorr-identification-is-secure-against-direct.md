# Schnorr identification is secure against direct attacks

Let $\mathbb{G}$ be a cyclic group of prime order $q$ with generator $g$, and consider Schnorr's identification protocol with challenges uniform in a set $C \subseteq \mathbb{Z}_q$ of size $N$. For every impersonation adversary $A$ in the direct-attack game with advantage $\varepsilon$ there is a discrete-logarithm algorithm $B$, running in about twice the time of $A$, with advantage $\varepsilon'$ satisfying $\varepsilon' \ge \varepsilon^2 - \varepsilon/N$; hence $\varepsilon \le 1/N + \sqrt{\varepsilon'}$. Under the discrete logarithm assumption and with superpolynomial $N$, the protocol is secure against direct attacks; since it is honest-verifier zero knowledge, it is also secure against eavesdropping attacks.

## Depends on

- [Discrete-logarithm experiment](../../public-key/hardness-assumptions/dlog-game.md)
- [Winning probability of a game](../../security-games/games-and-advantages/win-prob.md)
- [The Schnorr identification protocol as a Sigma protocol](../zero-knowledge-proofs/schnorr-sigma-protocol.md)

## Proof depends on

- [Special soundness](../schnorr-identification-scheme/extract-spec.md)
- [The rewinding lemma](the-rewinding-lemma.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Theorem 19.1
