---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Language.IsChomskyNormalForm
---

# Is Chomsky Normal Form

A grammar is in Chomsky normal form when every production has
output either two nonterminals, a single terminal, or the empty
word with the initial nonterminal on the left; and either the
initial nonterminal occurs in no output (so an empty production
cannot leak the empty word to other nonterminals) or there are no
empty outputs at all.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Computability.Languages.ContextFree.ChomskyNormalForm](../../../../../../sources/v2/CSLibExt.md)
