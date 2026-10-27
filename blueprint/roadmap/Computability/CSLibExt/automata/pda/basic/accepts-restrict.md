---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Automata.PDA.accepts_restrict
---

# Accepts restrict

Restricting the stack alphabet to a finite closed set does not change
the accepted language.

## Depends on

- [PDA](pda.md)
- [Closed Under](closed-under.md)
- [Accepts](accepts.md)
- [Restrict](restrict.md)

## Proof depends on

- [Config](config.md)
- [Derives](derives.md)
- [Derives restrict of derives](derives-restrict-of-derives.md)
- [Derives val of derives restrict](derives-val-of-derives-restrict.md)
- [Init Config](init-config.md)
- [Lift Stack](lift-stack.md)
- [Stack subset of derives](stack-subset-of-derives.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Automata.PDA.Basic](../../../../../../sources/v2/CSLibExt.md)
