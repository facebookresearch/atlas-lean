# Is Isofibration

A functor `F : C ⥤ D` is an isofibration when every isomorphism
`g : F.obj X ≅ Y` in `D` lifts strictly to an isomorphism in `C`:
there are `Y' : C`, `f : X ≅ Y'` and `h : F.obj Y' = Y` with
`F.mapIso f ≪≫ eqToIso h = g`.
