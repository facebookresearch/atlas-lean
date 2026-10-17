---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Recursive.computable_iff_nonempty_tm2Computable
---

# Turing computable equals recursive

**Turing computable equals recursive.** A function `ℕ → ℕ` is recursive iff a bundled
finite multi-stack machine (`FinTM2`) computes it under `encodeNat`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Turing-computable functions are recursive](of-tm2/part-02/computable-of-tm2-computable.md)
- [Recursive functions are Turing-computable](to-tm2/part-02/tm2-computable-of-computable.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Recursive.Equiv](../../../../../sources/v2/MathlibExt.md)
