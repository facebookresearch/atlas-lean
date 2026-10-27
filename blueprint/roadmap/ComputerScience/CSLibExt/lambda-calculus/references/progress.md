---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Languages.LambdaCalculus.References.progress
---

# Progress

Progress (TAPL Theorem 13.5.7): if `∅ | S ⊢ t : T` and `∅ | S ⊢ μ`, then
`t` is a value or `t | μ → t' | μ'` for some `t'` and `μ'`.

## Depends on

- [Has Type](typing/has-type.md)
- [Step](semantics/step.md)
- [Store](semantics/store.md)
- [Store Typed](typing/store-typed.md)
- [Term](syntax/term.md)
- [Value](syntax/value.md)
- [Ty](syntax/ty.md)

## Proof depends on

- [Lam of value](typing/lam-of-value.md)
- [Loc of value](typing/loc-of-value.md)
- [Exists of get Elem?](typing/exists-of-get-elem.md)
- [Instantiate](syntax/instantiate.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.References.Progress](../../../../../sources/v2/CSLibExt.md)
