---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Language.IsRegular.isContextFree
---

# Regular

Over a finite alphabet, every regular language is context-free.

Finiteness of the alphabet is necessary: a grammar has finitely many
productions, hence mentions only finitely many terminal symbols, but a DFA
over an infinite alphabet may accept every one-letter word.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Valuation](basic/part-01/is-valuation.md)
- [Derives append](basic/part-01/derives-append.md)
- [Eval Form](basic/part-01/eval-form.md)
- [Eval Symbol](basic/part-01/eval-symbol.md)
- [Language le of valuation](basic/part-01/language-le-of-valuation.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Languages.ContextFree.Regular](../../../../../sources/v2/CSLibExt.md)
