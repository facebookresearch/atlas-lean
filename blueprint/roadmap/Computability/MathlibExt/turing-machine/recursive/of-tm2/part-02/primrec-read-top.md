---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Recursive.primrec₂_readTop
---

# Primrec₂ read Top

The coded step. -/
noncomputable def stepC (c : CodedCfg tm) : Option (CodedCfg tm) :=
  c.1.map fun l ↦ stepAuxC tm (tm.m l) c.2.1 c.2.2

/-! ### The coded step is primitive recursive

## Depends on

- [Primcodable Arrow](../part-01/primcodable-arrow.md)
- [Primcodableσ](../part-01/primcodable-2.md)
- [Read Top](../part-01/read-top.md)

## Proof depends on

- [Decode](../part-01/decode.md)
- [Primrec₂ of eventually const](../part-01/primrec-of-eventually-const-2.md)
- [Sym List](../part-01/sym-list.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Recursive.OfTM2](../../../../../../../sources/v2/MathlibExt.md)
