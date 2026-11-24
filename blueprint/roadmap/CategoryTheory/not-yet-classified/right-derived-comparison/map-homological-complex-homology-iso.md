# Map Homological Complex Homology Iso

A functor preserving homology commutes with the homology functors on homological
complexes: `E.mapHomologicalComplex c ⋙ homologyFunctor B' c i ≅ homologyFunctor B c i ⋙ E`.

Both sides are, definitionally, `HomologicalComplex.shortComplexFunctor` followed by a
comparison of short-complex homology, so this is `ShortComplex.homologyFunctorIso E`
whiskered on the left.
