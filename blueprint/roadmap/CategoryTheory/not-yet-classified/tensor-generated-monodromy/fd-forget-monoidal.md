# Fd Forget Monoidal

The forgetful functor `FDRep k Γ ⥤ FGModuleCat k` is monoidal, for independent universes of
`k` and `Γ`. Mathlib's instance in `Mathlib.RepresentationTheory.Tannaka` covers equal universes,
so this one is only a local instance, used to build `fibreMonoidal`.
