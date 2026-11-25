# Ensemble-average error probability of random coding

Gallager's ensemble of codes with $M$ words of length $N$ picks the code words independently, and
every letter of every word independently with law $p$, so that the code
$C = (x_1, \dots, x_M)$ has probability $\prod_{m'} P(x_{m'})$. The ensemble-average error
probability of message $m$ is

$$\bar P_{e,m} = \sum_{C} \Big(\prod_{m'=1}^{M} P(x_{m'})\Big)\, P_{e,m}(C),$$

the sum running over all $M$-tuples of words.

## Background

- [Probability of a code word in Gallager's ensemble](block-input-prob.md)
- [Error probability of maximum-likelihood decoding](ml-error-prob.md)

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, Section II, equations (8) and (13).
