---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Language.YieldsContext
---

# Yields Context

A *semantic* derivation context: every word yielded by `B`,
framed by `l` and `r`, is yielded by `A`. This is the
language-inclusion form of a one-hole derivation context; it is
what pumping iteration uses, and it holds vacuously when `B`
yields nothing. The `YieldsContext.of_rule` lemma produces such
contexts from actual productions.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Yields](../yields/yields.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Languages.ContextFree.Pumping](../../../../../../sources/v2/CSLibExt.md)
