---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Language.IsContextFree.pumping
---

# Pumping

The pumping lemma for context-free languages: every context-free
language has a pumping length `n > 0` such that every word of length
at least `n` splits as `u ++ v ++ x ++ y ++ z` with `v ++ y` nonempty,
`v ++ x ++ y` of length at most `n`, and every pumped word
`u ++ v^[i] ++ x ++ y^[i] ++ z` (where `v^[i]` is `i` copies of `v`)
back in the language.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Reduced](../reduced/part-02/is-reduced.md)
- [Is Unit Output](../reduced/part-01/is-unit-output.md)
- [Length le of yields H](length-le-of-yields-h.md)
- [Yields](../yields/yields.md)
- [Ne nil of forall output ne nil](../reduced/part-01/ne-nil-of-forall-output-ne-nil.md)
- [Of yields H](of-yields-h.md)
- [Yields Context](yields-context.md)
- [Iterate](iterate.md)
- [Of rule](of-rule.md)
- [Yields H](yields-h.md)
- [Append](append.md)
- [Append inv](append-inv.md)
- [Mono](mono.md)
- [Exists minimal yields H](exists-minimal-yields-h.md)
- [Exists reduced grammar](../reduced/part-02/exists-reduced-grammar.md)
- [Form NTs](../reduced/part-01/form-nts.md)
- [Grammar NTs](../reduced/part-01/grammar-nts.md)
- [Mem language iff yields](../yields/mem-language-iff-yields.md)

## Sources

- [CSLibExt, CSLibExt.Computability.Languages.ContextFree.Pumping](../../../../../../sources/v2/CSLibExt.md)
