# Stamped modified nodal equations

For a real `n × m` matrix `B`, sets `R`, `L`, `C`, `S` of branches with values `(R_e)`, `(L_e)`,
`(C_e)` and source voltages `(E_e)`, a ground node `g`, node injections `j(t)`, node potentials
`v(t)`, inductor currents `i_L(t)` and voltage-source currents `i_V(t)`, the stamped equations hold
when, at every time `t`:

- `v(t)(g) = 0`;
- `G_C v'(t) + G_R v(t) + B_L i_L(t) + B_S i_V(t) = j(t)`, with the
  [nodal capacitance](nodal-capacitance.md) `G_C` and [nodal conductance](nodal-conductance.md) `G_R`;
- `diag(L) i_L'(t) - B_Lᵀ v(t) = 0`, with the [inductance matrix](inductance-diagonal.md);
- `B_Sᵀ v(t) = (E_e)_{e ∈ S}`.

Here `B_L` and `B_S` are the [inductor](inductor-incidence.md) and
[voltage-source](voltage-source-incidence.md) incidences, and derivatives are taken to be `0` where
the function is not differentiable.
