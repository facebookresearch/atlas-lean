---
article_id: af_8b6e1ebbbffceeb7d0c3c9a2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: NumberField.Modulus.finiteResidueMap_eq_one_of_valuation_le
---

# Finite Residue Map eq one of valuation le

Valuation criterion for triviality of the finite residue map: a valuation bound
on `z - 1` at every supported finite place forces `finiteResidueMap m z = 1`.

Source mapping (N406, Theorem 21.8, Section 21.3; ATLAS NumberTheoryI item N406):
the native-API finite-congruence step corresponding to
[`finitePartMapHom_ker_iff`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1996-L2011),
used by the weak-approximation argument before residue/sign surjectivity and by
[`theorem_21_8_quotient_iso`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L2607-L2647).
It is not the generalized weak-approximation theorem and not the final N406
result.

## Depends on

- [Finite Exponent](../../part-02/ray-group/finite-exponent.md)
- [Finite Residue Map](finite-residue-map.md)
- [Finite Supported](../../part-02/ray-group/finite-supported.md)
- [Ray Elements](../../part-02/ray-group/ray-elements.md)

## Proof depends on

- [Congruent One At Finite Part](../../part-02/ray-group/congruent-one-at-finite-part.md)
- [Finite Residue Map eq one iff](finite-residue-map-eq-one-iff.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NumberField.RayClass.FiniteCongruence](../../../../../../../../../sources/v2/MathlibExt.md)
