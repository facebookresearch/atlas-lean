# Single Mode Profile

Single-mode transient between a wall at rest at `y = 0` and a wall moving with velocity `A`
at `y = L` (for `L ≠ 0`, `singleModeProfile_walls`):
`U(t, y) = A y / L - (A / π) sin(π y / L) exp(-ν (π / L)² t)`, the plane Couette profile minus one
decaying sine mode. It is not a start from rest: for `L > 0` and `A ≠ 0` the initial data
`A y / L - (A / π) sin(π y / L)` is nonzero at every interior point `0 < y < L`, and the wall
`y = L` moves at every time.
