---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Automata.PDA.ClosedUnder
---

# Closed Under

A set of stack symbols is closed for `M` when pushing from a symbol in
the set only ever pushes symbols in the set. Computations starting inside
a closed set stay inside it.

## Depends on

- [PDA](pda.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Automata.PDA.Basic](../../../../../../sources/v2/CSLibExt.md)
