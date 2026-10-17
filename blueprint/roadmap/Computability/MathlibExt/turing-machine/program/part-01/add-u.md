---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.TM2Program.addU
---

# Add U

Stack `k` receives `i` more copies of the symbol `x` of the first entry `⟨k, x⟩` of `ps`
(`List.dlookup`); stacks without an entry are unchanged. The run lemmas assume `ps.NodupKeys`, so
the first entry is the only one.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Cnt](cnt.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Program](../../../../../../sources/v2/MathlibExt.md)
