# Balanced ports: the internal-energy rise is the pressure-drop power

For real `ρ`, `A`, `V`, `e_in`, `e_out`, `p_in`, `p_out`, `g`, `z` and a velocity `v ∈ ℝᵐ`, consider
a duct segment whose outlet and inlet faces both have area `A`, density `ρ`, velocity `v` and
elevation `z`, with outward normal velocity `V` at the outlet and `-V` at the inlet, and write the
outward port energy rate `E(vn, e, p) = A vn (ρ (e + |v|² / 2 + g z) + p)` of a face of area `A`
with outward normal velocity `vn`, density `ρ`, specific internal energy `e`, pressure `p`, velocity
vector `v ∈ ℝᵐ` (`|v|² = v · v`) and elevation `z` under gravity `g`. If the outward port energy
rates sum to zero, `E(V, e_out, p_out) + E(-V, e_in, p_in) = 0` (a steady segment without heat or
shaft work), then the internal-energy rise carried by the mass flow `ρ A V` equals the pressure-drop
power: `ρ (A V) (e_out - e_in) = (p_in - p_out) (A V)`. This is one direction of the
[port balance](port-energy-rate-add-eq-zero-iff.md).
