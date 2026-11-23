# Encryption from hard-core predicates

Goldreich's general form of probabilistic encryption (*Foundations of Cryptography*, Vol. II,
Construction 5.3.13): from a collection of trapdoor permutations $p_\alpha$ with a hard-core predicate
$b$, encrypt a bit $\sigma$ as $(p_\alpha(r), \sigma \oplus b(r))$ for a uniform $r$ in the domain;
the owner of the trapdoor inverts $p_\alpha$ and recovers $\sigma$. If $b$ is hard-core, encryptions
of $0$ and $1$ cannot be told apart (Proposition 5.3.14); with the Goldreich–Levin theorem, which
gives every one-way permutation a hard-core predicate, this yields public-key encryption from any
trapdoor permutation (Theorem 5.3.15).

Here the construction is stated for one key distribution and a finite domain. The security
theorem is **per adversary**: the advantage of any distinguisher between encryptions of $0$ and $1$ is
exactly twice the prediction advantage of a predictor that calls it once, which carries over to
efficient adversaries. An all-predictor form ("if every predictor wins with probability at most
$\tfrac12 + \varepsilon$, then …") would be vacuous in this concrete model: an unbounded predictor
inverts $p_\alpha$ and always wins, so its hypothesis forces $\varepsilon \ge \tfrac12$. Such a form
needs a resource-bounded class of predictors.

## The scheme

- [Encryption of one bit with a hard-core predicate](scheme.md)
- [Correctness of encryption with a hard-core predicate](scheme-correct.md)

## Hard-core experiments

- [The hard-core experiment, distinguishing form](hc-exp.md)
- [Hard-core distinguishing advantage](hc-advantage.md)
- [The hard-core prediction experiment](predict-game.md)
- [Negating a distinguisher](win-prob-hc-exp-not.md)

## From distinguishing to predicting

- [The predictor built from a distinguisher](predictor.md)
- [The coins of the predictor](predictor-coins.md)
- [The predictor's success for one key and one coin](win-prob-inner.md)
- [Distinguishing implies predicting](win-prob-predict-game-predictor.md)

## Security

- [Distinguishing encryptions is distinguishing the hard-core bit](ind-exp-scheme.md)
- [Goldreich's Proposition 5.3.14, per adversary](ind-advantage-eq-two-mul-predict-advantage.md)

## Unbounded predictors

- [An unbounded predictor always wins](half-le-of-forall-predict-le.md)

## Related topics

- [Semantic security and indistinguishability](../../security-games/semantic-security-and-indistinguishability/README.md): the security notions achieved.
- [Goldwasser–Micali encryption](../goldwasser-micali-encryption/README.md): the original
  probabilistic encryption scheme, from quadratic residuosity.
- [Goldreich–Levin theorem](../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/goldreich-levin-theorem/README.md):
  the hard-core predicate that every one-way permutation has.
- [RSA cryptosystem](../rsa-cryptosystem/README.md): a candidate trapdoor permutation.
