---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Recursive.computable_of_tm2Computable
---

# Turing-computable functions are recursive

**Turing-computable functions are recursive.** A function `ℕ → ℕ` computed by a bundled
finite multi-stack machine (`FinTM2`) under the binary encoding `encodeNat` is `Computable`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Coded Cfg](../part-01/coded-cfg.md)
- [Relevant](../part-01/relevant-2.md)
- [Bits Val](../part-01/bits-val.md)
- [Code](../part-01/code.md)
- [Decode](../part-01/decode.md)
- [Enc](../part-01/enc.md)
- [Enc Stk](../part-01/enc-stk.md)
- [Encode Nat eq cons](../part-01/encode-nat-eq-cons.md)
- [Opt Step C](opt-step-c.md)
- [Opt Step C iterate](opt-step-c-iterate.md)
- [Partrec run](../part-01/partrec-run.md)
- [Primcodable Arrow](../part-01/primcodable-arrow.md)
- [PrimcodableΛ](../part-01/primcodable.md)
- [Primcodableσ](../part-01/primcodable-2.md)
- [Primrec of eventually const](../part-01/primrec-of-eventually-const.md)
- [Primrec₂ of finite left](../part-01/primrec-of-finite-left.md)
- [Primrec₂ read Top](primrec-read-top.md)
- [Pushes](../part-01/pushes.md)
- [Read Top](../part-01/read-top.md)
- [Relevant](../part-01/relevant.md)
- [Relevant init List](relevant-init-list.md)
- [Running before halt](running-before-halt.md)
- [Step Aux C](../part-01/step-aux-c.md)
- [Step C](step-c.md)
- [Sym List](../part-01/sym-list.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Recursive.OfTM2](../../../../../../../sources/v2/MathlibExt.md)
