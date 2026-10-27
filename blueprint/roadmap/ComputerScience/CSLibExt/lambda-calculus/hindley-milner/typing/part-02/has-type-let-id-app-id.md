---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.HindleyMilner.hasType_let_id_app_id
---

# `let` generalizes

**`let` generalizes**: `let f = λx. x in f f` has type `α → α`.

## Depends on

- [Ctx](../part-01/ctx.md)
- [Expr](../part-01/expr.md)
- [Has Type](../part-01/has-type.md)
- [Term](../../../../unification/basic/part-01/term.md)

## Proof depends on

- [Ftv](../part-01/ftv.md)
- [Lookup](../part-01/lookup.md)
- [Scheme](../part-01/scheme.md)
- [Eval](../part-01/eval.md)
- [Inst](../part-01/inst.md)
- [Ty](../part-01/ty.md)
- [Above](above.md)
- [Gen](../part-01/gen.md)
- [To Scheme](../part-01/to-scheme.md)
- [Subst](../../../../unification/basic/part-01/subst-2.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.HindleyMilner.Typing](../../../../../../../sources/v2/CSLibExt.md)
