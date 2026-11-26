# The translation to locally nameless terms

The locally nameless form of a named term:
the variable `x` becomes the free variable `fvar x`, an application is translated
componentwise, and `λx.M` becomes `abs` of the translation of `M` closed for `x` at index `0`,
so that the occurrences of `x` bound by this binder become bound indices.
