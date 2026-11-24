# Book value under depreciation with a salvage floor

Book value under a salvage-floor depreciation recursion with charge rule
`charge(n, v)`: `V(0) = cost` and `V(n + 1) = max(salvage, V(n) - charge(n, V(n)))`.
In period `n` the charge depends on the current book value, but the asset is
never written below `salvage`. Straight-line (`charge(n, v) = c`) and
declining-balance (`charge(n, v) = r * v`) schedules are special cases.
