# Stand force from the port balance

Take the axial momentum balance of the control volume
in the port form of `ControlVolumes.hasDerivAt_momentum_twoPort`: the momentum rate `P'` is the
inflow `ṁ_in v_in + ṁ_f v_f` minus the outflow `ṁ_out v_e`, minus the port pressure forces with
outward normals `-1` (inlet) and `+1` (exhaust), plus the ambient force `F_lat` on the rest of the
surface and the axial force `F` of the stand on the contents. A uniform ambient pressure has zero
resultant over the closed surface (`hamb`). Then `F = T + P' - ṁ_f v_f`.
