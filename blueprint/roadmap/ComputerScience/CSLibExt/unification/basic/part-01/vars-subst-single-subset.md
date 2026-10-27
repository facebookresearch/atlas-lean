---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Unification.Term.vars_subst_single_subset
---

# Vars subst single subset

Substituting `t` for `x` removes `x` when `x` does not occur in `t`, and adds only the
variables of `t`.

## Depends on

- [Term](term.md)
- [Subst](subst-2.md)
- [Vars](vars.md)

## Sources

- [CSLibExt, CSLibExt.Foundations.Unification.Basic](../../../../../../sources/v2/CSLibExt.md)
