---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Language.fromCnfNT
---

# From Cnf NT

Read a basic nonterminal of the binarized grammar back as a
symbol of `g`; out-of-range indices (never produced by `toCnfNT` on
grammar symbols) decode to the initial nonterminal.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Grammar Terminals](grammar-terminals.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Languages.ContextFree.ChomskyNormalForm](../../../../../../sources/v2/CSLibExt.md)
