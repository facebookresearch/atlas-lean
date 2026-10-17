---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Program.cmpB_run
---

# Comparison

**Comparison.** With bit blocks `u` on `a` and `w` on `b`, `cmpB` ends at `eqL` if `u = w` and
at `neL` otherwise, after `c.length + 1` steps where `c` is a common prefix of `u` and `w` (their
longest one: after `c` the two blocks have no common next bit). The bits of `c` have moved from
`a` and `b` to the scratch stacks `ta` and `tb`; no other stack changes.

## Depends on

- [Distinct4](distinct4.md)
- [Ends Bit Block](ends-bit-block.md)
- [Flag](../program/part-01/flag.md)
- [Is Bit Block](is-bit-block.md)
- [Run](../program/part-01/run.md)
- [Cmp B](cmp-b.md)

## Proof depends on

- [Cmp B last](cmp-b-last.md)
- [Cmp B prefix](cmp-b-prefix.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.BitOps](../../../../../sources/v2/MathlibExt.md)
