---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Language.anbncnLang_not_isContextFree
---

# Anbncn Lang not is Context Free

The language `a^n b^n c^n` is not context-free, by the pumping
lemma: pumping `a^n b^n c^n` down would keep the three letter counts
equal, so the pumped factor has equal counts of all letters, but a
short factor misses `a` or `c`, forcing the factor to be empty.

## Depends on

- [Anbncn Lang](anbncn-lang.md)

## Proof depends on

- [Pumping](../pumping/pumping.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Languages.ContextFree.NonClosure](../../../../../../sources/v2/CSLibExt.md)
