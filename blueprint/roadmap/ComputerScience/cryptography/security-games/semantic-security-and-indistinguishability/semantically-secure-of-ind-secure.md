# Indistinguishability implies semantic security, all-adversary form

Let $\varepsilon \ge 0$ and suppose that a public-key scheme has
[indistinguishable encryptions with error $\varepsilon$](ind-secure.md) and that for each length $n$
of a message there is a dummy message of length $n$. Then the scheme is
[semantically secure with error $\varepsilon$](semantically-secure.md), for any types of a priori
information and of guesses, with the [simulator](simulator.md) as ideal adversary.

For a correct public-key scheme with two distinct messages of the same length the hypothesis fails
for every $\varepsilon < 1$ ([unattainability](not-ind-secure-of-correct.md)), so in this unbounded
model the implication relates statements that are trivially true or false. The content is the
[per-adversary form](win-prob-ss-real-le.md).

## Informally uses

- [Indistinguishability implies semantic security, per adversary](win-prob-ss-real-le.md)

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.2, Theorem 5.2.5 and Proposition 5.2.6 (stated there for private-key schemes; Goldreich notes
  that the public-key analogue is proved in the same way, with the encryption key given to the
  adversary).
