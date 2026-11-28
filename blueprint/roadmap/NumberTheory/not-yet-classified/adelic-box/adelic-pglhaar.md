# Haar measure on adelic `PGL(2)`

Let `R` be a Dedekind domain with fraction field `K`, and
assume that adelic `PGL(2)` is a topological group and locally compact (the instance arguments
`IsTopologicalGroup (AdelicPGL2 R K)` and `LocallyCompactSpace (AdelicPGL2 R K)`). Then
`adelicPGLHaar R K` is a Haar measure for the Borel measurable space `pglBorel R K`: Mathlib's
`MeasureTheory.Measure.haar`, which gives measure `1` to an arbitrarily chosen positive compact
set. Mathlib's quotient-group instances supply the first assumption for every such `R`, and the
second when `AdeleRing R K` is locally compact, as for `R = 𝓞 K` over a number field `K`. The
results about `adelicPGLHaar` (`isHaarMeasure_adelicPGLHaar`, `adelicPGLHaar_image_pos`,
`adelicPGLHaar_image_lt_top_of_subset`) also assume that `K` is a number field and that `R` is a
free `ℤ`-module of finite rank.
