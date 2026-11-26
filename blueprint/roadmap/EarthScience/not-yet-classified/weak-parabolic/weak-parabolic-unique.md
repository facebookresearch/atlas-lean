# Uniqueness of weak solutions of `∂ₜu = ∂ₓ(κ ∂ₓu) + F` on `(0, 1)`

Let `κ` be a.e. strongly measurable on the rectangle `[t0, t1] × [0, 1]` with
`0 < kmin ≤ κ ≤ kmax` a.e. Two solutions `(u, ux)` and `(u', ux')` of the class
`IsWeakParabolicSolution` with the same forcing `F` and the same initial value `u0`,
`u t0 = u0 = u' t0` in `L²(0,1)`, agree in `L²(0,1)` at every time of `[t0, t1]`.

The energy identity `‖w τ‖² + 2 ∫_{t0}^{τ} ∫₀¹ κ (∂ₓw)² = ‖w t0‖²` for the solutions `w` of
the homogeneous equation (`F = 0`) in the same class is an explicit hypothesis, `hEnergyId`.
It is the energy identity of weak solutions (Evans, §5.9.2, Theorem 3, applied as in the
uniqueness proof of §7.1.2), which holds for every such `κ`; this module does not prove it.
The proof subtracts the two solutions, which gives a solution of the homogeneous equation
with zero initial value, and the identity with `κ ≥ kmin > 0` forces its `L²(0,1)` norm to
vanish at every time.
