# Port energies balance iff internal-energy rise equals pressure power

For real `ρ`, `A`, `V`, `e_in`, `e_out`, `p_in`, `p_out`, `g`, `z` and a velocity `v ∈ ℝᵐ`, consider
a duct segment whose outlet and inlet faces both have area `A`, density `ρ`, velocity `v` and
elevation `z`, with outward normal velocity `V` at the outlet and `-V` at the inlet, and write the
outward port energy rate `E(vn, e, p) = A vn (ρ (e + |v|² / 2 + g z) + p)` of a face of area `A`
with outward normal velocity `vn`, density `ρ`, specific internal energy `e`, pressure `p`, velocity
vector `v ∈ ℝᵐ` (`|v|² = v · v`) and elevation `z` under gravity `g`. Then the outward port energy
rates sum to zero, `E(V, e_out, p_out) + E(-V, e_in, p_in) = 0`, if and only if the internal-energy
rise carried by the mass flow `ρ A V` equals the pressure-drop power:
`ρ (A V) (e_out - e_in) = (p_in - p_out) (A V)`. The flow work `p A vn` is counted once, inside the
port rates. The identity holds for all real values.
