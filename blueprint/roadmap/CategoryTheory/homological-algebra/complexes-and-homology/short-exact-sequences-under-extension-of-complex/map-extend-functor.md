# Map extend Functor

Extension along an arbitrary embedding of complex shapes preserves short exactness.

The proof is degreewise in the target shape via
`HomologicalComplex.shortExact_iff_degreewise_shortExact`.  For a degree outside
the image of the embedding every component of the extended complexes is zero.  For a
degree inside the image we transport along the canonical isomorphisms
`HomologicalComplex.extendXIso` and use `HomologicalComplex.extendMap_f` to check
that the degreewise short complexes are isomorphic.
