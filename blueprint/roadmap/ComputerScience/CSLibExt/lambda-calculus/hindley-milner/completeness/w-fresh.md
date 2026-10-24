---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.HindleyMilner.W_fresh
---

# Freshness

**Freshness**: if the free variables of `Γ` are below `n`, then W's counter does not
decrease, and its type and the values of its substitution at variables below `n` use only
variables below the returned counter.

## Depends on

- [Ctx](../typing/part-01/ctx.md)
- [Ftv](../typing/part-01/ftv.md)
- [Expr](../typing/part-01/expr.md)
- [Ty](../typing/part-01/ty.md)
- [Vars Below](vars-below.md)
- [W](../algorithm-w/w.md)
- [Subst](../../../unification/basic/part-01/subst.md)

## Proof depends on

- [Lookup](../typing/part-01/lookup.md)
- [Subst](../typing/part-01/subst.md)
- [Visible Vars](../typing/part-01/visible-vars.md)
- [Scheme](../typing/part-01/scheme.md)
- [Bound Sup](../algorithm-w/bound-sup.md)
- [Eval](../typing/part-01/eval.md)
- [Inst](../typing/part-01/inst.md)
- [Subst Ty](../typing/part-01/subst-ty.md)
- [Gen](../typing/part-01/gen.md)
- [To Scheme](../typing/part-01/to-scheme.md)
- [Comp](../../../unification/basic/part-01/comp.md)
- [Term](../../../unification/basic/part-01/term.md)
- [Exists of mem vars subst](../../../unification/basic/part-01/exists-of-mem-vars-subst.md)
- [Subst](../../../unification/basic/part-01/subst-2.md)
- [Vars](../../../unification/basic/part-01/vars.md)
- [Eq Vars](../../../unification/basic/part-01/eq-vars.md)
- [Unify](../../../unification/basic/part-02/unify.md)
- [Vars unify subset](../../../unification/basic/part-02/vars-unify-subset.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.HindleyMilner.Completeness](../../../../../../sources/v2/CSLibExt.md)
