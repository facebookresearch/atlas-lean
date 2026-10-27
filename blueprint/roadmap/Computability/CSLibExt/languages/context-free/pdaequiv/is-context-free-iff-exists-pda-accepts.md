---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Language.isContextFree_iff_exists_pda_accepts
---

# Is Context Free iff exists pda accepts

Over an alphabet in `Type`, the context-free languages are exactly
the languages accepted by empty stack by finite pushdown automata whose
transitions consume letters from a finite set.

## Depends on

- [PDA](../../../automata/pda/basic/pda.md)
- [Accepts](../../../automata/pda/basic/accepts.md)

## Proof depends on

- [Closed Under](../../../automata/pda/basic/closed-under.md)
- [Accepts restrict](../../../automata/pda/basic/accepts-restrict.md)
- [Mem restrict step](../../../automata/pda/basic/mem-restrict-step.md)
- [Restrict](../../../automata/pda/basic/restrict.md)
- [Cfg PDA accepts](../pda/cfg-pda-accepts.md)
- [Is Context Free accepts](is-context-free-accepts.md)
- [Cfg PDA](../pda/cfg-pda.md)
- [Cfg Step](../pda/cfg-step.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Languages.ContextFree.PDAEquiv](../../../../../../sources/v2/CSLibExt.md)
