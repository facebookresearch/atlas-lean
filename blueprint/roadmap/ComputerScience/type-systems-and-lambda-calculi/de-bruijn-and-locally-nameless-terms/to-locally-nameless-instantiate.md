# β-substitution is opening

If the body `b` is scoped at `names.length + 1` and the
argument `a` is scoped at the length of `names`, then translating the contractum
`instantiate b a` is opening the translation of `b`, one binder deep, with the translation of
`a`.
