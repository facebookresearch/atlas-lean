# If cost ≥ salvage, nonnegative charges never raise book value

If the asset starts at or above salvage (`salvage ≤ cost`) and the charge
`charge(n, v)` is nonnegative at every book value `v ≥ salvage`, then book value
under the salvage-floor recursion never increases: `V(n + 1) ≤ V(n)` for every
`n`. This covers declining-balance rules such as `charge(n, v) = r * v` with
`0 ≤ r` and `0 ≤ salvage`, whose charge is negative only below zero.
