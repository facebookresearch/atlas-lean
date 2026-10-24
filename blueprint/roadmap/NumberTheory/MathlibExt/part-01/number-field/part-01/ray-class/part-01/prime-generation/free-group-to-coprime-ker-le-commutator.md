---
article_id: af_9333f258b6ea1f4f4701c285
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: NumberField.Modulus.freeGroupToCoprime_ker_le_commutator
---

# Free Group To Coprime ker le commutator

The kernel of the free-group presentation lies in the commutator subgroup,
the direct native counterpart of ATLAS `freeGroupToCoprime_ker_le_commutator`
(source lines 429--487). The prime basis-vector computation at source lines
416--427 is replaced by
`FractionalIdeal.factorizationMulEquiv_primeUnitFractionalIdeal`. The proof
builds the ATLAS retraction to the abelianization through
`FractionalIdeal.factorizationMulEquiv`,
`Finsupp.comapDomain.addMonoidHom`, `Finsupp.toFreeAbelianGroup`, and
`Abelianization.of`; the retraction itself stays private to this proof.

## Depends on

- [Coprime Primes](coprime-primes.md)
- [Coprime Fractional Ideals](../../part-02/ray-group/coprime-fractional-ideals.md)
- [Free Group To Coprime](free-group-to-coprime.md)

## Proof depends on

- [Factorization Mul Equiv](../../../../../../../../RingTheory/MathlibExt/dedekind-domain/factorization-equiv/factorization-mul-equiv.md)
- [Factorization Mul Equiv prime Unit Fractional Ideal](../prime-generators/factorization-mul-equiv-prime-unit-fract.md)
- [Finite Supported](../../part-02/ray-group/finite-supported.md)
- [Free Group To Coprime of](free-group-to-coprime-of.md)
- [Prime Coprime Unit](../prime-generators/prime-coprime-unit.md)
- [Prime Unit Fractional Ideal](../prime-generators/prime-unit-fractional-ideal.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NumberField.RayClass.PrimeGeneration](../../../../../../../../../sources/v2/MathlibExt.md)
