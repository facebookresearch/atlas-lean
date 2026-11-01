---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Languages.LambdaCalculus.References.preservation
---

# Preservation

Preservation (TAPL Theorem 13.5.3): a step from a well-typed configuration
leads to a configuration that is well typed, with the same type, under an
extension of the store typing.

## Depends on

- [Has Type](../typing/has-type.md)
- [Step](../semantics/step.md)
- [Store](../semantics/store.md)
- [Store Typed](../typing/store-typed.md)
- [Term](../syntax/term.md)
- [Ty](../syntax/ty.md)

## Proof depends on

- [Extend Store](extend-store.md)
- [Instantiate](instantiate.md)
- [Append](append.md)
- [Exists of get Elem?](../typing/exists-of-get-elem.md)
- [Set](set.md)
- [Value](../syntax/value.md)
- [Instantiate](../syntax/instantiate.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.References.Preservation](../../../../../../sources/v2/CSLibExt.md)
