---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Recursive.main_phase
---

# Main phase

The main phase: `tr` evaluates `c` on `[n]`, and the wrapped machine follows it into the
post-phase.

## Depends on

- [FCfg](../part-01/fcfg.md)
- [FΓ](../part-01/f.md)
- [FΛ](../part-01/f-2.md)
- [Phase](../part-01/phase.md)
- [Frun](../part-01/frun.md)
- [Mk Stk](../part-01/mk-stk.md)
- [Start mem](../part-01/start-mem.md)
- [Supp](../part-01/supp.md)

## Proof depends on

- [FStmt](../part-01/fstmt.md)
- [Label Rel](label-rel.md)
- [Tr Rel](tr-rel.md)
- [Exists iterate eq of reaches](exists-iterate-eq-of-reaches.md)
- [Fstep](../part-01/fstep.md)
- [Fwd Prog](../part-01/fwd-prog.md)
- [Lift Stk](lift-stk.md)
- [Restrict](../part-01/restrict.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Recursive.ToTM2](../../../../../../../sources/v2/MathlibExt.md)
