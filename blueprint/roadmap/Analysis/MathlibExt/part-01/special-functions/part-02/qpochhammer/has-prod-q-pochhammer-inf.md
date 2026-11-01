---
article_id: af_fec32e0861e6c2efdeaaa5de
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.QPochhammer.hasProd_qPochhammerInf
---

# Has Prod q Pochhammer Inf

Convergence of the complex q-Pochhammer infinite product on the
open unit disk.

Source `2607.10576:D01`: the infinite product `(a;q)_∞` is used under
`‖q‖ < 1`. For complex `a, q` with `‖q‖ < 1` the factor family
`n ↦ 1 - a * q ^ n` satisfies `HasProd` to the named value
`qPochhammerInf a q hq`. No nonvanishing hypothesis is imposed, so
zero-factor cases (product value `0`) are covered.

## Depends on

- [Q Pochhammer Inf](q-pochhammer-inf.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.QPochhammer](../../../../../../../sources/v2/MathlibExt.md)
