# With the Darcy loss the internal-energy rise is nonnegative

For real `ρ`, `A`, `V`, `e_in`, `e_out`, `p_in`, `p_out`, `g`, `z` and a velocity `v ∈ ℝᵐ`, consider
a duct segment whose outlet and inlet faces both have area `A`, density `ρ`, velocity `v` and
elevation `z`, with outward normal velocity `V` at the outlet and `-V` at the inlet, and write the
outward port energy rate `E(vn, e, p) = A vn (ρ (e + |v|² / 2 + g z) + p)` of a face of area `A`
with outward normal velocity `vn`, density `ρ`, specific internal energy `e`, pressure `p`, velocity
vector `v ∈ ℝᵐ` (`|v|² = v · v`) and elevation `z` under gravity `g`. Suppose the port rates sum to
zero, `E(V, e_out, p_out) + E(-V, e_in, p_in) = 0`, and the pressure drop is the
[friction loss](friction-pressure-drop.md) `p_in - p_out = c Q |Q|` at `Q = A V`, with `c ≥ 0`. Then
the internal-energy rise is `ρ (A V) (e_out - e_in) = c Q² |Q|`, and it is nonnegative, in both flow
directions.
