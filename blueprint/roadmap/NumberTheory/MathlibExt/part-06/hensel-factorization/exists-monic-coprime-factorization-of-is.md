---
article_id: af_afd8016af467a39b833c3a62
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Polynomial.exists_monic_coprime_factorization_of_isAdicComplete
---

# Exists monic coprime factorization of is Adic Complete

Standard monic Hensel factor lifting, generic in the ideal.

If `A` is `I`-adically complete and a monic polynomial `f` reduces modulo `I`
to a product of monic coprime polynomials, the factorization lifts to `A`.
The proof packages the residue factorization via the universal coprime
factorization ring, lifts its structure map through `I`-adic completeness,
and evaluates the universal factors over `A`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.HenselFactorization](../../../../../sources/v2/MathlibExt.md)
