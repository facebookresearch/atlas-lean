# Semantic security and indistinguishability

Goldwasser and Micali's definition of secure encryption: a ciphertext must not help any efficient
adversary compute any partial information on the plaintext (*semantic security*), and the technical
condition that implies it, that encryptions of any two messages of equal length cannot be told apart
(*indistinguishability of encryptions*). The two notions are equivalent (Goldreich, *Foundations of
Cryptography*, Vol. II, Theorem 5.2.5).

Here both are stated for public-key schemes in concrete form: one fixed scheme, adversaries given as
functions of their random coins, an explicit error $\varepsilon$ in place of Goldreich's $1/p(n)$, and
no bound on running time. The theorems that matter are **per adversary**: a distinguisher with
advantage $\varepsilon$ against the hardwired plaintexts gives semantic security with error
$\varepsilon$ against the given adversary, and a distinguisher with advantage $\delta$ gives an
adversary that beats every simulator by $\delta/2$. Each transformation makes one call to the given
adversary, so it carries over to efficient adversaries, which is what Goldreich's asymptotic
Theorem 5.2.5 needs.

Against unbounded adversaries, which this model allows, no correct public-key scheme has
indistinguishable encryptions with an error below $1$, or is semantically secure with an error below
$\tfrac12$: a distinguisher may decrypt with any secret key matching the public key. The
all-adversary implications between the two definitions also hold, but for public-key schemes
they relate statements that are trivially true or false; they are labelled "all-adversary form".

## Indistinguishability of encryptions

- [The indistinguishability experiment](ind-exp.md)
- [Distinguishing advantage between encryptions](ind-advantage.md)
- [Indistinguishability of encryptions with error $\varepsilon$](ind-secure.md)
- [$\mathsf{PubK}^{\mathrm{eav}}$ with fixed messages is the indistinguishability experiment](pub-cpa-exp-eq-ind-exp.md)

## Semantic security

- [The real semantic-security experiment](ss-real.md)
- [The ideal semantic-security experiment](ss-ideal.md)
- [Semantic security with error $\varepsilon$](semantically-secure.md)

## Indistinguishability implies semantic security

- [The simulator of Goldreich's Proposition 5.2.6](simulator.md)
- [The distinguisher hardwiring one plaintext](ss-distinguisher.md)
- [Indistinguishability implies semantic security, per adversary](win-prob-ss-real-le.md)
- [Indistinguishability implies semantic security, all-adversary form](semantically-secure-of-ind-secure.md)

## Semantic security implies indistinguishability

- [Semantic security implies indistinguishability, per adversary](win-prob-ss-real-two-point.md)
- [Semantic security implies indistinguishability, all-adversary form](ind-secure-of-semantically-secure.md)

## Unattainability against unbounded adversaries

- [Indistinguishability is unattainable against unbounded distinguishers](not-ind-secure-of-correct.md)
- [Semantic security is unattainable against unbounded adversaries](not-semantically-secure-of-correct.md)

## Related topics

- [Games and advantages](../games-and-advantages/README.md): the averaging lemmas the reductions use.
- [Goldwasser–Micali encryption](../../public-key/goldwasser-micali-encryption/README.md): the first scheme proved
  semantically secure, from the hardness of deciding quadratic residuosity.
- [ElGamal encryption](../../public-key/elgamal-encryption/README.md): an eavesdropping (indistinguishability)
  security proof from the decisional Diffie–Hellman assumption.
- [Encryption from hard-core predicates](../../public-key/encryption-from-hard-core-predicates/README.md):
  Goldreich's construction of public-key encryption from a trapdoor permutation and a hard-core
  predicate (Construction 5.3.13, Proposition 5.3.14).
