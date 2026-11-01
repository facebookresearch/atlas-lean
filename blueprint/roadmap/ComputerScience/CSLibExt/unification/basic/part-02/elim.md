---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Unification.UnifySpec.elim
---

# Elim

The elimination step: if the unifiers of `e :: E` are those sending `x` to `t.subst s` and
unifying `E`, then the specification passes from `substEqs (single x t) E` to `e :: E`.

## Depends on

- [Equations](../part-01/equations.md)
- [Subst](../part-01/subst.md)
- [Comp](../part-01/comp.md)
- [Single](../part-01/single.md)
- [Term](../part-01/term.md)
- [Subst](../part-01/subst-2.md)
- [Vars](../part-01/vars.md)
- [Unify Spec](unify-spec.md)
- [Subst Eqs](../part-01/subst-eqs.md)

## Proof depends on

- [Single comp eq](../part-01/single-comp-eq.md)
- [Subst single of not mem](../part-01/subst-single-of-not-mem.md)
- [Unifies](../part-01/unifies.md)

## Sources

- [CSLibExt, CSLibExt.Foundations.Unification.Basic](../../../../../../sources/v2/CSLibExt.md)
