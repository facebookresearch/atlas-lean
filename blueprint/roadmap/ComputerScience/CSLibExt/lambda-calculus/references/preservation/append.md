---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Languages.LambdaCalculus.References.StoreTyped.append
---

# Append

Allocation: appending a value of type `T` to a well-typed store gives a
store that is well typed under the store typing extended by `T`.

## Depends on

- [Has Type](../typing/has-type.md)
- [Store](../semantics/store.md)
- [Store Typed](../typing/store-typed.md)
- [Term](../syntax/term.md)
- [Value](../syntax/value.md)
- [Ty](../syntax/ty.md)

## Proof depends on

- [Extend Store](extend-store.md)
- [Extend Store](extend-store-2.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.References.Preservation](../../../../../../sources/v2/CSLibExt.md)
