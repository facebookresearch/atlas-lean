---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Language.IsContextFree.exists_pda_accepts
---

# Exists pda accepts

Every context-free language is accepted by empty stack by a one-state
pushdown automaton whose stack alphabet is the grammar's symbols.

## Depends on

- [PDA](../../../automata/pda/basic/pda.md)
- [Accepts](../../../automata/pda/basic/accepts.md)

## Proof depends on

- [Cfg PDA accepts](cfg-pda-accepts.md)
- [Cfg PDA](cfg-pda.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Languages.ContextFree.PDA](../../../../../../sources/v2/CSLibExt.md)
