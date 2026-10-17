---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Unification.vars_unify_subset
---

# Vars unify subset

`unify` introduces no variables: each value of its result uses only the variable itself
and the variables of the equations.

## Depends on

- [Equations](../part-01/equations.md)
- [Subst](../part-01/subst.md)
- [Vars](../part-01/vars.md)
- [Eq Vars](../part-01/eq-vars.md)
- [Unify](unify.md)

## Proof depends on

- [Comp](../part-01/comp.md)
- [Single](../part-01/single.md)
- [Term](../part-01/term.md)
- [Size](../part-01/size.md)
- [Card eq Vars elim lt](card-eq-vars-elim-lt.md)
- [Eq Size](../part-01/eq-size.md)
- [Subst Eqs](../part-01/subst-eqs.md)
- [Vars single comp subset](vars-single-comp-subset.md)

## Sources

- [CSLibExt, CSLibExt.Foundations.Unification.Basic](../../../../../../sources/v2/CSLibExt.md)
