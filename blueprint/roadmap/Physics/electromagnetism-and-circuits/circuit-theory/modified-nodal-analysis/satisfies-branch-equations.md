# Branch equations of a linear network

For a real `n × m` matrix `B`, sets `R`, `L`, `C`, `S` of branches with values `(R_e)`, `(L_e)`,
`(C_e)` and source voltages `(E_e)`, a ground node `g`, node injections `j(t)`, node potentials
`v(t)`, branch voltages `v_b(t)` and branch currents `i_b(t)`, the branch equations hold when, at
every time `t`:

- `v(t)(g) = 0`, `v_b(t) = Bᵀ v(t)` and `B i_b(t) = j(t)`;
- `v_b(t)_e = R_e i_b(t)_e` for `e ∈ R`, `i_b(t)_e = C_e (v_b)_e'(t)` for `e ∈ C`,
  `v_b(t)_e = L_e (i_b)_e'(t)` for `e ∈ L`, and `v_b(t)_e = E_e` for `e ∈ S`.

Time derivatives are taken to be `0` where the function is not differentiable.
