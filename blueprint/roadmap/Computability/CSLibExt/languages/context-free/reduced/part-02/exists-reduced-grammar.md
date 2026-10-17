---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Language.exists_reduced_grammar
---

# Exists reduced grammar

Every grammar has a reduced grammar (no empty output, no unit
output) generating its language minus the empty word.

## Depends on

- [Is Unit Output](../part-01/is-unit-output.md)

## Proof depends on

- [Unit Steps](../part-01/unit-steps.md)
- [Cases of mem unit Grammar rules](../part-01/cases-of-mem-unit-grammar-rules.md)
- [Eps Grammar](../part-01/eps-grammar.md)
- [Eps Grammar language](../part-01/eps-grammar-language.md)
- [Eps Grammar output ne nil](../part-01/eps-grammar-output-ne-nil.md)
- [Unit Grammar](../part-01/unit-grammar.md)
- [Unit Grammar language](unit-grammar-language.md)
- [Unit Grammar not is Unit Output](../part-01/unit-grammar-not-is-unit-output.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Languages.ContextFree.Reduced](../../../../../../../sources/v2/CSLibExt.md)
