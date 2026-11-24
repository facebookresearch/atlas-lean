# Nine Lemma Middle

Let `C` be an additive category with an exact structure, and let
`D : ShortComplex (ShortComplex C)` be a short complex of short complexes.
Its rows are `D.X₁`, `D.X₂`, and `D.X₃`; its columns are the short complexes
`D.map ShortComplex.π₁`, `D.map ShortComplex.π₂`, and
`D.map ShortComplex.π₃`. All row and column composites are therefore zero,
and the squares commute. If the three columns and the top and bottom rows
are admissible exact, then the middle row `D.X₂` is admissible exact.
In particular, the middle row is already a short complex, not just a pair
of maps in a commuting grid.
