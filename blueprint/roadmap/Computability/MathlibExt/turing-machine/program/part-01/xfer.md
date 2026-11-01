---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.TM2Program.xfer
---

# Xfer

Loop: pop stack `k` until empty; for each popped symbol push one unit on every target in
`ps`. `ps = []` drains `k`, `ps = [⟨t, x⟩]` moves the counter, two targets copy it.

## Depends on

- [Flag](flag.md)

## Proof depends on

- [Push All](push-all.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Program](../../../../../../sources/v2/MathlibExt.md)
