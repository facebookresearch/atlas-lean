---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Automata.PDA.restrict
---

# Restrict

Restrict the stack alphabet to a finite closed set `Γ₀` containing the
initial stack symbol. The restricted PDA is over the subtype, hence has a
`Fintype` stack alphabet, and accepts the same language
(`PDA.accepts_restrict`).

## Depends on

- [PDA](pda.md)
- [Closed Under](closed-under.md)

## Proof depends on

- [Lift Stack](lift-stack.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Automata.PDA.Basic](../../../../../../sources/v2/CSLibExt.md)
