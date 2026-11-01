---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.ComplexityTheory.comp_mem_P
---

# Comp mem P

`P` is closed under polynomial-time preimages: if `L ∈ P` and `f` is polynomial-time,
then `L ∘ f ∈ P`. In particular `P` is closed under polynomial-time many-one reductions.

## Depends on

- [Bitstring Encoding](../../../complexity/bitstring-encoding.md)
- [Bit Decode](../../../complexity/bit-decode.md)
- [Bit Decode bit Encode](../../../complexity/bit-decode-bit-encode.md)
- [Bit Encode](../../../complexity/bit-encode.md)
- [Delimit](../../../complexity/delimit.md)
- [Undelimit](../../../complexity/undelimit.md)
- [Undelimit Blocks](../../../complexity/undelimit-blocks.md)
- [Undelimit Blocks Aux](../../../complexity/undelimit-blocks-aux.md)
- [Decision Complexity Class](../../../complexity/decision-complexity-class.md)
- [Decision Problem](../../../complexity/decision-problem.md)
- [Is Poly Time](../../../complexity/is-poly-time.md)
- [P](../../../complexity/p.md)

## Proof depends on

- [Comp](comp-2.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Composition](../../../../../../sources/v2/MathlibExt.md)
