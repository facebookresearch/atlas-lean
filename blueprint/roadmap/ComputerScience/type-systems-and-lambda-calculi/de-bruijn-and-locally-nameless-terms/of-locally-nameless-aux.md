# Locally nameless terms as de Bruijn terms, under binders

`ofLocallyNamelessAux depth
names M` translates `M` as if it stood under `depth` abstractions in the naming context `names`.
A bound variable `bvar i` becomes the index `i`, and a free name `x` becomes the index
`depth + names.idxOf x`, which is `depth + names.length` when `x` is not in `names`. Applications
are translated componentwise, and the body of an abstraction one binder deeper.
