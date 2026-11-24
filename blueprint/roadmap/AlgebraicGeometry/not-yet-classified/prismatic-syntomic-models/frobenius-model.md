# Frobenius Model

Completed Frobenius is construction output normalized on actual source coordinates.
The covering requirement keeps these normalization tests nonvacuous on every basis object.

The normalization pins the evaluated Frobenius only on the image of the uncompleted coordinates
`N^{≥i}Δ_S → Δ_S`; the complexes `T.nygaard i` and `T.complex i` are Nygaard-completed, and the
continuous extension (from the Nygaard topology to the `(p, I)`-adic one) that determines it on
the completion is not encoded. So a `FrobeniusModel` is not unique, and statements that depend on
the choice of Frobenius are requested for a model chosen jointly with them.
