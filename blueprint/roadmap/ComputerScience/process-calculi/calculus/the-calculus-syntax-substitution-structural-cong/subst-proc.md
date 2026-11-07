# Substitution of a name into a π-calculus process at a cutoff

Substitute the name `n` for the variable at `cutoff` in a
process. Under a binder, `n` is lifted by one at cutoff `0` so it
keeps referring to the same outer names: every free index of `n`
refers to a binder above the substitution point, so all of them shift.
Lifting at the current cutoff would leave indices below the cutoff
captured by the new binder.
