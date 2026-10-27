---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Languages.LambdaCalculus.References.typeSafety
---

# Type Safety

Type safety: a closed term that is well typed in a well-typed store never
evaluates to a stuck configuration; every reachable term is a value or can
step.

## Depends on

- [Has Type](../typing/has-type.md)
- [Step](../semantics/step.md)
- [Steps](../semantics/steps.md)
- [Store](../semantics/store.md)
- [Store Typed](../typing/store-typed.md)
- [Term](../syntax/term.md)
- [Value](../syntax/value.md)
- [Ty](../syntax/ty.md)

## Proof depends on

- [Preservation](preservation-2.md)
- [Progress](../progress.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.References.Preservation](../../../../../../sources/v2/CSLibExt.md)
