---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.TM2Recursive.restrict
---

# Restrict

A statement of `tr` as a statement of the wrapped machine: stacks move to `inl`, jumps stay
inside `supp c` (by `hq`), and `halt` jumps to the post-phase.

## Depends on

- [FStmt](fstmt.md)
- [Supp](supp.md)

## Proof depends on

- [FΓ](f.md)
- [FΛ](f-2.md)
- [Phase](phase.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Recursive.ToTM2](../../../../../../../sources/v2/MathlibExt.md)
