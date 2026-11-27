# Goldreich's Proposition 5.3.14, per adversary

For every distinguisher $A$, its [advantage](../../security-games/semantic-security-and-indistinguishability/ind-advantage.md) between encryptions of $0$ and
$1$ under the [scheme](scheme.md) equals $2 \lvert \Pr[\text{the predictor built from } A \text{ wins}]
- \tfrac12 \rvert$, twice the prediction advantage of the [predictor](predictor.md) built from $A$
with one call. So a distinguisher with advantage $\varepsilon$ gives a predictor of the hard-core bit
with advantage $\varepsilon/2$, and an efficient distinguisher an equally efficient predictor: this is
the security of encryption from a hard-core predicate, in the form that carries over to efficient
adversaries.

## Informally uses

- [Distinguishing encryptions is distinguishing the hard-core bit](ind-exp-scheme.md)
- [Distinguishing implies predicting](win-prob-predict-game-predictor.md)

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.3.4, Proposition 5.3.14.
