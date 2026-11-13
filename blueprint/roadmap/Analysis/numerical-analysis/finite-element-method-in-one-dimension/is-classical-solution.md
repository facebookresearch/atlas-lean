# Classical solution of the Dirichlet problem $-u'' = f$

`u` is a classical solution of `-u'' = f` on `(0, 1)` with
`u(0) = u(1) = 0`. We ask `u` to be `C²` on all of `ℝ`, which is no loss for
the interval problem (a `C²` function on `[0, 1]` extends), and `f` to be continuous.
The equation is stated on the open interval, as in the Dirichlet problem: requiring it
at the endpoints without regularity of `f` would be a genuine strengthening. With `f`
continuous, endpoint equality follows by continuity (`eq_Icc`), and the integral proofs
use that derived version.
