# Renaming the variables of a term

Given a renaming `ρ` of de Bruijn indices, renaming a
term by `ρ` replaces each free variable `i` by `ρ i`; under the binder of an abstraction body
the renaming is lifted, sending `0` to `0` and `i + 1` to `ρ i + 1`.
