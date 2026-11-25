# Feasible DC dispatch

Consider a network with finitely many buses `v` and branches `e` (each with a tail and a head bus
and a real susceptance `b_e`), finitely many generators `g` placed at buses, a demand `d`, a
reference bus `r`, generator limits `p_min`, `p_max` and branch-flow limits `f_min`, `f_max`. A
generation `p` and angles `θ` form a feasible dispatch if

- `L_b θ = C p - d` (nodal balance), with the
  [weighted Laplacian](../dc-power-flow/weighted-laplacian.md) `L_b = B diag(b) Bᵀ` and the
  [generator incidence](generator-incidence.md) `C`;
- `θ_r = 0`;
- `p_min,g ≤ p_g ≤ p_max,g` for every generator;
- `f_min,e ≤ f_e ≤ f_max,e` for every branch, with the
  [DC branch flow](../dc-power-flow/dc-branch-flow.md) `f_e = b_e (θ_tail(e) - θ_head(e))`.
