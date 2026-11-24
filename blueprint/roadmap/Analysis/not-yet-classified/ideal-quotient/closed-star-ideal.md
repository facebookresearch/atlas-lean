# Closed Star Ideal

A closed two-sided star ideal in a complex nonunital C-star algebra.

The ideal stores its closedness and two-sidedness proofs without installing
either proof globally.  Quotient constructions below activate them only in a
local `letI` scope and delegate to `NonUnitalStarSubalgebra.Quotient`.
