---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.HindleyMilner.not_hasType_lam_self_app
---

# Self-application has no type

**Self-application has no type**: in `λf. f f`, `f` is λ-bound and so monomorphic.

## Depends on

- [Ctx](../part-01/ctx.md)
- [Expr](../part-01/expr.md)
- [Has Type](../part-01/has-type.md)
- [Ty](../part-01/ty.md)

## Proof depends on

- [Lookup](../part-01/lookup.md)
- [Scheme](../part-01/scheme.md)
- [Eval](../part-01/eval.md)
- [Inst](../part-01/inst.md)
- [Gen](../part-01/gen.md)
- [Substitution lemma](has-type-var-iff.md)
- [Ne node self left](ne-node-self-left.md)
- [To Scheme](../part-01/to-scheme.md)
- [Term](../../../../unification/basic/part-01/term.md)
- [Subst](../../../../unification/basic/part-01/subst-2.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.HindleyMilner.Typing](../../../../../../../sources/v2/CSLibExt.md)
