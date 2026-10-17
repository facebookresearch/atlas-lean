---
article_id: af_2ae40660378ab61add3c7846
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MonoidHom.isDirichletCharacterModulus_iff
---

# Is Dirichlet Character Modulus iff

ATLAS `NumberTheoryI` Lemma 18.8: `χ` with least positive period `m` is a
Dirichlet character of modulus `m'` iff `m ∣ m'` and `m' ∣ m ^ k` for some `k`.
Forward: minimality gives the divisibility, and a prime divisor of `m'` divides
`m` (else `χ p` is simultaneously zero and nonzero).  Backward: periodicity
lifts along `m ∣ m'`, and the nonvanishing locus transfers via the two lemmas
above.  The `Nontrivial R` hypothesis is sharp: the subsingleton monoid with zero
satisfies the remaining typeclasses while forcing every `χ n = 0`, which
falsifies the claimed nonvanishing locus.

## Depends on

- [Is Dirichlet Character Modulus](is-dirichlet-character-modulus.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.DirichletCharacter.Period](../../../../../../sources/v2/MathlibExt.md)
