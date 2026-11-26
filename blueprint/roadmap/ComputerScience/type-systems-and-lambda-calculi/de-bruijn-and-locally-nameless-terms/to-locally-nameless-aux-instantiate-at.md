# β-substitution at a depth is opening

If `a` is scoped at the length of `names` and `b` is
scoped at `depth + 1 + names.length`, then translating `instantiateAt depth a b` under `depth`
binders is opening, at index `depth`, the translation of `b` one binder deeper with the
translation of `a`.
