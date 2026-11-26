# Sequential repetition gives negligible soundness while preserving zero knowledge

If an auxiliary-input zero-knowledge proof for $L$ has soundness error $s < 1$ (constant), then its $k(n)$-fold sequential repetition, with $k(n) = \omega(\log n)$ (for example $k = n + 1$ giving error $s^{n+1}$), has negligible soundness error and remains auxiliary-input zero knowledge.

## Proof sketch

Soundness errors multiply under sequential repetition. For zero knowledge, simulate the rounds one by one, passing the cheating verifier's state as auxiliary input to the single-round simulator; a hybrid argument bounds the distinguishing advantage by $k$ times the single-round advantage.

## Depends on

- [Auxiliary-input computational zero knowledge](auxiliary-input-zero-knowledge.md)

## Proof depends on

- [Soundness error of sequential repetition](../../zero-knowledge-proofs/soundness-error-of-sequential-repetition.md)
- [Hybrid argument](../../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
