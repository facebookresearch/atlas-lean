---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Unification.Term.size_subst_lt_of_mem
---

# Size subst lt of mem

A variable occurring in a term properly inside it makes the term strictly larger than any
substituted copy of the variable, so `var x = t` has no unifier when `x` occurs in `t ≠ var x`
(the occurs check).

## Depends on

- [Subst](subst.md)
- [Term](term.md)
- [Size](size.md)
- [Subst](subst-2.md)
- [Vars](vars.md)

## Sources

- [CSLibExt, CSLibExt.Foundations.Unification.Basic](../../../../../../sources/v2/CSLibExt.md)
