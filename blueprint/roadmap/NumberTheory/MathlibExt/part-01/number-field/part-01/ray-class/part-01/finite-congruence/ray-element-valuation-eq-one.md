---
article_id: af_513349a12157c137ac176f71
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: NumberField.Modulus.rayElement_valuation_eq_one
---

# Ray Element valuation eq one

A ray element has valuation one at every finite prime supported by the modulus.
Source (N406 §21.3): the supported-finite-place fact; compare
[`valuation_eq_one_of_spanSingleton_coprime'`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/RayClassFields.lean#L1206-L1248)
and `hx_coprime`.

## Depends on

- [Finite Supported](../../part-02/ray-group/finite-supported.md)
- [Ray Elements](../../part-02/ray-group/ray-elements.md)

## Proof depends on

- [Ray Element count span Singleton eq zero](ray-element-count-span-singleton-eq-zero.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NumberField.RayClass.FiniteCongruence](../../../../../../../../../sources/v2/MathlibExt.md)
