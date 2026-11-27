# Finite of finite

If `f : R →+* S` is finite, a finite `S`-module `M` is finite as an `R`-module via `f`.
The `R`-action is `Module.compHom M f` and finiteness follows from the tower `R → S → M`
and `Module.Finite.trans`.
