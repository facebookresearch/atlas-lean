# Distinguishing implies predicting

For every distinguisher $A$, the [predictor built from $A$](predictor.md), with
[its coins](predictor-coins.md), wins the [prediction experiment](predict-game.md) with probability

$$\tfrac12 + \tfrac12 \bigl(\Pr[A = 1 \text{ in world } 0] - \Pr[A = 1 \text{ in world } 1]\bigr),$$

the probabilities being those of the [hard-core experiment](hc-exp.md). This exact identity is the
step that Goldreich's proof of Proposition 5.3.14 obtains "analogously to the second proof of
Theorem 3.4.1" of his Volume I.

## Informally uses

- [The predictor's success for one key and one coin](win-prob-inner.md)
- [Averaging an affine identity](../../security-games/games-and-advantages/win-prob-bind-affine.md)

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.3.4, proof of Proposition 5.3.14.
- O. Goldreich, *Foundations of Cryptography, Vol. I: Basic Tools*, Cambridge University Press, 2001, second proof of Theorem 3.4.1, to which Volume II refers for this step (Volume I was not consulted).
