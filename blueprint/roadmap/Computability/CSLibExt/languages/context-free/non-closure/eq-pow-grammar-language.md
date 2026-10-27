---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Language.eqPowGrammar_language
---

# Eq Pow Grammar language

The grammar `S → a S b | ε` generates `a^n b^n`.

## Depends on

- [Eq Pow Grammar](eq-pow-grammar.md)
- [Eq Pow Lang](eq-pow-lang.md)

## Proof depends on

- [Yields](../yields/yields.md)
- [Append](../yields/append.md)
- [Eval Form](../basic/part-01/eval-form.md)
- [Eval Symbol](../basic/part-01/eval-symbol.md)
- [Language le of valuation](../basic/part-01/language-le-of-valuation.md)
- [Mem language iff yields](../yields/mem-language-iff-yields.md)
- [Yields of rule](../yields/yields-of-rule.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Languages.ContextFree.NonClosure](../../../../../../sources/v2/CSLibExt.md)
