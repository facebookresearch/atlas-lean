# Semantic security implies indistinguishability, all-adversary form

Let $\varepsilon \ge 0$. If a public-key scheme is
[semantically secure with error $\varepsilon$](semantically-secure.md), already for trivial a priori
information and Boolean guesses, then it has
[indistinguishable encryptions with error $2\varepsilon$](ind-secure.md).

The proof applies semantic security to the adversaries that run a distinguisher $D$ and its negation
on the [two-point instance](win-prob-ss-real-two-point.md); the factor $2$ comes from that instance.
For a correct public-key scheme the hypothesis fails for every $\varepsilon < \tfrac12$
([unattainability](not-semantically-secure-of-correct.md)); the content is the
[per-adversary form](win-prob-ss-real-two-point.md).

## Informally uses

- [Semantic security implies indistinguishability, per adversary](win-prob-ss-real-two-point.md)

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.2, Theorem 5.2.5 and Proposition 5.2.7 (stated for private-key schemes; the public-key
  analogue is the same argument with the encryption key given to the adversary).
