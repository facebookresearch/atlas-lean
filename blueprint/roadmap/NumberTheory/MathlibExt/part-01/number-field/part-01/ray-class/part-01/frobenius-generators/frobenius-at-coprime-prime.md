---
article_id: af_e1afa686edadd937afe641ee
declaration: def
origin: cited
statement: formalized
lean: NumberField.Modulus.frobeniusAtCoprimePrime
---

# Frobenius At Coprime Prime

Chosen Frobenius at a privately chosen unramified prime above `p`: the
arithmetic Frobenius of `Gal (L / K)` acting on `𝓞 L` at the privately chosen
prime above `p`. Takes the unramifiedness-outside-`m` witness so that the
value is the chosen Frobenius at an unramified prime, not an arbitrary lift
modulo inertia. Equality across different primes is deferred to the abelian
choice-independence stage.

## Depends on

- [Coprime Primes](../prime-generation/coprime-primes.md)
- [Is Unramified Outside](is-unramified-outside.md)

## Proof depends on

- [Finite Supported](../../part-02/ray-group/finite-supported.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NumberField.RayClass.FrobeniusGenerators](../../../../../../../../../sources/v2/MathlibExt.md)
