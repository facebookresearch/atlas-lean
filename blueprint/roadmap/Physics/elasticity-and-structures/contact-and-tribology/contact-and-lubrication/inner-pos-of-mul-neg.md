# Inner pos of mul neg

Control, invalid sign: if `μ * N < 0`, the stick rule admits no traction
(`‖t‖ ≤ μ * N < 0` is impossible), so every Coulomb traction is a sliding one and the friction
law supplies positive power. The sign in `IsCoulombTraction.inner_eq_and_nonpos` therefore
needs `0 ≤ μ * N`; both `μ < 0 < N` and `N < 0 < μ` reverse it.
