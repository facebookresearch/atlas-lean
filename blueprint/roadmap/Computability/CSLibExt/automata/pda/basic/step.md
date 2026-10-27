---
declaration: inductive
origin: cited
statement: formalized
lean: Cslib.Automata.PDA.Step
---

# Step

One computation step: pop the top stack symbol, optionally consume one
input letter, move to the chosen state, and push the chosen list.

## Depends on

- [PDA](pda.md)
- [Config](config.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Automata.PDA.Basic](../../../../../../sources/v2/CSLibExt.md)
