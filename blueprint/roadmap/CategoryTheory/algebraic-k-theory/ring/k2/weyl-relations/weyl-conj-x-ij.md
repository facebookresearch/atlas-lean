# Weyl conj x ij

Weyl conjugation of the same ordered root `x i j` by `weyl i j` :
`w_{ij}(u) x_{ij}(a) w_{ij}(u)⁻¹ = x_{ji}(-u⁻¹ a u⁻¹)`.
Coefficient and sign are obtained from the checked-in
`weyl_conj_x_ji` and `weyl_neg_eq_inv`; no guess.
`w_{ij}(-u)=w_{ij}(u)⁻¹`, `w_{ij}(-u) x_{ji}(b) w_{ij}(-u)⁻¹ = x_{ij}(-(-u) b (-u))`,
and with `b = -u⁻¹ a u⁻¹` we have `-(-u) b (-u) = -u b u = a`,
so `x_{ij}(a)=w_{ij}(-u) x_{ji}(b) w_{ij}(-u)⁻¹` and conjugating by
`w_{ij}(u)` gives `x_{ji}(b)`.
