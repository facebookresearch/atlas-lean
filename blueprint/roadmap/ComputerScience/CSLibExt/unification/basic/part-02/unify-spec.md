---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Unification.UnifySpec
---

# Unify Spec

What `unify` guarantees: a returned substitution is a unifier through which every
unifier `s'` factors as `s ≫ s'`, and failure means there is no unifier.

## Depends on

- [Equations](../part-01/equations.md)
- [Subst](../part-01/subst.md)

## Proof depends on

- [Comp](../part-01/comp.md)
- [Unifies](../part-01/unifies.md)

## Sources

- [CSLibExt, CSLibExt.Foundations.Unification.Basic](../../../../../../sources/v2/CSLibExt.md)
