# Conservation iff rankine Hugoniot

Rankine-Hugoniot from two classical sides.

A scalar conservation law `u_t + f(u)_x = 0` holds classically on each side
of an interface `x = s τ` that is differentiable at time `t` with speed `c`
and lies strictly inside the fixed interval `[a, b]`. The left state is a
field `uL` that is jointly continuous, with jointly continuous time partial
`vL`, on an open set `UL` containing the closed left slice `{t} × [a, s t]`
(a smooth neighbourhood reaching across the interface, so the one-sided
trace `uL t (s t)` is a value of a continuous field); symmetrically `uR`,
`vR` on `UR ⊇ {t} × [s t, b]`. At time `t` the spatial flux derivatives
`gL`, `gR` exist on the open side intervals, the flux composites are
continuous on the closed side intervals, and the side equations
`vL t x + gL x = 0`, `vR t x + gR x = 0` hold on the open side intervals.

Then the split mass on `[a, b]` changes at the conservation rate
`f (uL t a) - f (uR t b)` (flux in at `a` minus flux out at `b`) exactly
when the Rankine-Hugoniot jump identity
`c * (uR t (s t) - uL t (s t)) = f (uR t (s t)) - f (uL t (s t))` holds.
This is the classical Rankine-Hugoniot condition for scalar conservation laws
(Evans, *Partial Differential Equations*, §3.4.1; LeVeque, *Finite Volume Methods
for Hyperbolic Problems*, §11.8). No existence of such solutions is asserted.
