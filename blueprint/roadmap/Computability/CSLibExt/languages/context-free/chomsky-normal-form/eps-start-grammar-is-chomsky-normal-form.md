---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Language.epsStartGrammar_isChomskyNormalForm
---

# Eps Start Grammar is Chomsky Normal Form

The fresh-start construction preserves Chomsky normal form for
grammars with no empty outputs. The no-empty-outputs hypothesis is
essential: an existing empty production would be embedded with the
old initial nonterminal, not the fresh one, on the left.

## Depends on

- [Is Chomsky Normal Form](is-chomsky-normal-form.md)
- [Eps Start Grammar](eps-start-grammar.md)

## Proof depends on

- [Eps Start Grammar initial not mem output](eps-start-grammar-initial-not-mem-output.md)
- [Map Rule](../basic/part-01/map-rule.md)
- [Map Rule injective](../basic/part-01/map-rule-injective.md)
- [Map Symbol](../basic/part-01/map-symbol.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Languages.ContextFree.ChomskyNormalForm](../../../../../../sources/v2/CSLibExt.md)
