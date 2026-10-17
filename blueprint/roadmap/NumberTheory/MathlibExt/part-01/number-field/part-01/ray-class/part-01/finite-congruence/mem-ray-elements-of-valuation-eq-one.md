---
article_id: af_aa1c66da91ea9858b03daee5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: NumberField.Modulus.mem_rayElements_of_valuation_eq_one
---

# Mem ray Elements of valuation eq one

Valuation-one criterion for ray elements: if the normalized valuation of `a`
is one at every finite prime supported by `m`, then the principal fractional
ideal `(a)` has count zero at each such prime, so `a ∈ rayElements m`.

This is the converse of `rayElement_valuation_eq_one`: the converse valuation
criterion used to turn the controlled approximation witness into a ray element.
It is a reusable bridge toward N406, not itself the full source theorem.

## Depends on

- [Finite Supported](../../part-02/ray-group/finite-supported.md)
- [Ray Elements](../../part-02/ray-group/ray-elements.md)

## Proof depends on

- [Coprime Fractional Ideals](../../part-02/ray-group/coprime-fractional-ideals.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NumberField.RayClass.FiniteCongruence](../../../../../../../../../sources/v2/MathlibExt.md)
