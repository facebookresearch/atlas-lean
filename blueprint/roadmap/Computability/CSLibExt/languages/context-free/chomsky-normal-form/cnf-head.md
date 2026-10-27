---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Language.cnfHead
---

# Cnf Head

The head of a binarized output: two basic nonterminals, a basic
nonterminal followed by a chain nonterminal for the remaining
suffix, or a single terminal for a lone wrapper. Unit and empty
inputs (excluded for reduced grammars) get the empty output.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Grammar Terminals](grammar-terminals.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Languages.ContextFree.ChomskyNormalForm](../../../../../../sources/v2/CSLibExt.md)
