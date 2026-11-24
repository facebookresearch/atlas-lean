# Parcel steps of a burning mass history and their continuum limit

Let `M : ℝ → ℝ` be differentiable at `t` with `M'(t) = m' < 0` and `M(t) > 0`, and let `v`, `ve` and
`F` be real. For `h > 0` let `q_h = (M(t) − M(t + h)) / h`, the rate of the mass expelled in the
forward step from `t` to `t + h`. Then:

- `q_h → −m'` as `h → 0⁺`;
- for all sufficiently small `h > 0`: the expelled mass `M(t) − M(t + h)` is nonnegative, the
  remaining mass `M(t) − q_h h` equals `M(t + h)` and is positive, and the parcel step from the
  state `(M(t), v)` with flow `q_h` conserves momentum,
  `M(t + h) v_h + (M(t) − M(t + h)) (v − ve) = M(t) v + F h`, where `v_h` is the
  [parcel velocity](parcel-velocity.md);
- the slope `(v_h − v) / h` tends to `(F − ve m') / M(t)` as `h → 0⁺`, the acceleration `a` of
  the reduced law `M a = −ve M' + F`.
