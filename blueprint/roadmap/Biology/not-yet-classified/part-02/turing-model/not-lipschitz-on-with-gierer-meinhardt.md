# Boundary case: Gierer–Meinhardt

The kinetics `(a - b u + u² / v, u² - v)` are not
Lipschitz on the closed unit ball of `ℝ²`, because of the `u² / v` term near `v = 0`. So the
route `exists_lipschitzOnWith_closedBall_of_contDiff` / `lipschitzOnWith_nemytskii` to the
hypothesis `hF` of the flow interface is closed, and `localFlow` does not apply to them without
an invariant region bounding `v` away from `0`. (For nonempty `K`, restricting to constant fields
shows that the Nemytskii operator itself fails `hF`; that corollary is not formalized here.)
