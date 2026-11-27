# The ring of integers of a 13th cyclotomic field is principal

For any number field $K$ that is a $13$th cyclotomic extension of $\mathbb Q$, every ideal of $\mathcal O_K$ is principal. The field is arbitrary subject to the cyclotomic hypothesis, not a particular presentation of $\mathbb Q(\zeta_{13})$.

## Proof depends on

- [Minkowski bound](../../../algebraic-number-theory/number-fields-embeddings/minkowski-bound.md)
- [Reusable principal prime-ideal certificate](principal-prime-cyclotomic-certificate.md)

## Proof outline

Certify the exponent-thirteen Minkowski cutoff of 306 and use the inertia degrees to remove primes whose ideals have norm above it. For the remaining cases, check the cited explicit principal-ideal certificates above 3, 13, 53, 79, 131 and 157; in particular 13 is ramified and needs its own calculation. Match these to the general Minkowski criterion, using the Galois action on ideals above each rational prime. The exponent-eleven calculation supplies a method, not the certificates for degree twelve.

## Sources

- Anthropic, [IsCyclotomicExtension.Rat.thirteen_pid](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Theorems/Thm_IsCyclotomicExtension_Rat_thirteen_pid.lean#L6).
- Anthropic, [the proof route](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/PROOF-PATH.md).
- Anthropic, [the explicit arithmetic proof](https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_IsCyclotomicExtension_Rat_thirteen_pid.lean#L622-L722).
