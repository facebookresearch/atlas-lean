# Parcel steps of a linear burning mass history

Let `M(t + h) = M(t) + m' h` for every real `h`, with `m' < 0` and `M(t) > 0`, and let `v`, `ve` and
`F` be real. For every step `h > 0` that leaves positive mass, `M(t + h) > 0` (that is,
`h < M(t) / (−m')`), the expelled mass `M(t) − M(t + h)` is nonnegative, its rate
`(M(t) − M(t + h)) / h` is exactly `−m'`, the remaining mass `M(t) − (−m') h` is `M(t + h)`, and the
parcel step from `(M(t), v)` with the constant flow `−m'` conserves momentum,
`M(t + h) v_h + (M(t) − M(t + h)) (v − ve) = M(t) v + F h`, with `v_h` the
[parcel velocity](parcel-velocity.md). Its slope `(v_h − v) / h` tends to `(F − ve m') / M(t)` as
`h → 0⁺`. A longer step would leave no mass or negative mass, and is not a parcel step.
