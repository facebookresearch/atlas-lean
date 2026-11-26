# De Bruijn terms as locally nameless terms, under binders

`toLocallyNamelessAux depth
names t` translates `t` as if it stood under `depth` abstractions in the naming context `names`,
whose head is the innermost free name. An index `i < depth` becomes the bound variable `bvar i`,
an index `depth + j` with `j < names.length` becomes the free variable `fvar names[j]`, and every
larger index `i` becomes the dangling bound variable `bvar i`. Applications are translated
componentwise, and the body of an abstraction one binder deeper.
