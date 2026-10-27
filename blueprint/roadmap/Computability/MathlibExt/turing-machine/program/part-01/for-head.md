---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.TM2Program.forHead
---

# For Head

Loop head: pop counter `c`. If a unit was popped, push one unit on the index stack `cd` and
run the body from `body`; if `c` is empty go to `rest` (which restores `c` from `cd`).

## Depends on

- [Flag](flag.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Program](../../../../../../sources/v2/MathlibExt.md)
