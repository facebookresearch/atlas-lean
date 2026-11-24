# Stand force from the axial momentum balance

Let `ṁ_in`, `v_in`, `p_in`, `A_in`, `ṁ_f`, `v_f`, `ṁ_out`, `v_e`, `p_e`, `A_e`, `p_a`, `F_lat`, `F`
and `P'` be reals with `F_lat + p_a A_in − p_a A_e = 0` (a uniform ambient pressure has zero
resultant over the closed surface, `F_lat` acting on the part outside the ports) and the axial
momentum balance `P' = ṁ_in v_in + ṁ_f v_f − ṁ_out v_e − (−p_in A_in + p_e A_e) + F_lat + F` (inlet
and exhaust ports with outward normals `−1` and `+1`, fuel feed `ṁ_f` at axial velocity `v_f`, and
`F` the axial force of the stand on the contents). Then `F = T + P' − ṁ_f v_f`, with
`T = ṁ_out v_e − ṁ_in v_in + (p_e − p_a) A_e − (p_in − p_a) A_in` the
[separate-flow thrust](separate-flow-thrust.md).
