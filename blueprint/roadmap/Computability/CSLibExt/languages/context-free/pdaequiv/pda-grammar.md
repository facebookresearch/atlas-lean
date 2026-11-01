---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Language.pdaGrammar
---

# Pda Grammar

The triple grammar of a pushdown automaton: nonterminals `none` (the
initial one) and `some (p, γ, q)`, deriving the words that pop `γ` while
going from state `p` to state `q`. Transitions are only used for letters
in `T₀` (plus `ε`-transitions).

## Depends on

- [PDA](../../../automata/pda/basic/pda.md)

## Proof depends on

- [State Lists](state-lists.md)
- [Step Rule](step-rule.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Languages.ContextFree.PDAEquiv](../../../../../../sources/v2/CSLibExt.md)
