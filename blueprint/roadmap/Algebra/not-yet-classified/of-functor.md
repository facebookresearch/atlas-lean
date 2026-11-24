# Of Functor

`ofFunctor` is the object-level inverse to `HomologicalComplex.asFunctor`: it turns a
diagram `K : J ⥤ HomologicalComplex C c` into a complex in the functor category
`HomologicalComplex (J ⥤ C) c`.  The degree `n` is the composite `K ⋙ eval C c n`, and
the differential is pointwise the differential of `K.obj j`, with naturality coming from
the fact that `K.map f` is a chain map.
