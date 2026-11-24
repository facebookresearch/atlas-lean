# Parcel continuum linear

A linear mass history `M (t + h) = M t + m' h` that is burning, `m' < 0`. Every forward step
`h > 0` that leaves positive mass, `0 < M (t + h)` (that is, `h < M t / (-m')`), expels the
nonnegative mass `M t - M (t + h)` at exactly the constant rate `-m'`, and the parcel step with the
constant flow `-m'` leaves exactly the mass `M (t + h)` and conserves momentum: there it is the
actual parcel step. A longer step would leave no mass or negative mass, and is not a parcel step.
The slope of the constant-flow step tends to `(F - ve m') / M t` as `h → 0⁺`.
