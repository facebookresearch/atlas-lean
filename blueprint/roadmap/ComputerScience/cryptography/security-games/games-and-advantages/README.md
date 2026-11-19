# Games and advantages

The averaging lemmas behind the security reductions: games are distributions on $\{0, 1\}$, a game
that first draws a value from a distribution $\mu$ and then runs a game depending on it succeeds with
the average success probability, and pointwise bounds, affine identities and identities between sums
survive this averaging. The two-point distribution is the plaintext distribution of Goldreich's
Proposition 5.2.7.

- [Success probability of an average](win-prob-bind.md)
- [Averaging a pointwise bound](win-prob-bind-le.md)
- [Averaging an affine identity](win-prob-bind-affine.md)
- [Averaging a pointwise identity between sums of success probabilities](apply-true-bind-add-eq.md)
- [The two-point distribution](two-point.md)
- [Averaging over the two-point distribution](win-prob-two-point-bind.md)
- [A game that never outputs $\neg b$ always outputs $b$](eq-pure-of-not-mem-support.md)

## Related topics

- [Semantic security and indistinguishability](../semantic-security-and-indistinguishability/README.md)
- [Goldwasser–Micali encryption](../../public-key/goldwasser-micali-encryption/README.md)
- [Encryption from hard-core predicates](../../public-key/encryption-from-hard-core-predicates/README.md)
