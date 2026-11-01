---
declaration: def
origin: cited
statement: formalized
lean: Cslib.HindleyMilner.Ctx.ftv
---

# Ftv

The free type variables of a context: those of its visible bindings. A binding shadowed
by an earlier one with the same name does not count, so `Γ.ftv` depends only on `Γ.lookup`.

## Depends on

- [Ctx](ctx.md)

## Proof depends on

- [Visible Vars](visible-vars.md)
- [Scheme](scheme.md)

## Sources

- [CSLibExt, CSLibExt.Languages.LambdaCalculus.HindleyMilner.Typing](../../../../../../../sources/v2/CSLibExt.md)
