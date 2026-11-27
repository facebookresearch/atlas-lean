# The de Bruijn round trip, under binders

If `names` has no repetition and `t` is scoped at
`depth + names.length`, then translating `t` to a locally nameless term and back gives `t`.
