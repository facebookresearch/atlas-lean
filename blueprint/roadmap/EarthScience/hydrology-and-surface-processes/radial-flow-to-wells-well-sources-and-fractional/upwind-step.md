# Upwind Step

One normalized upwind step on the chain `s : Fin (n + 1) → ℝ` with inflow state `sIn` at the
left boundary: cell `i` uses `Matrix.vecCons sIn s i.castSucc`, which is `sIn` for the first cell
and `s (i - 1)` otherwise.
