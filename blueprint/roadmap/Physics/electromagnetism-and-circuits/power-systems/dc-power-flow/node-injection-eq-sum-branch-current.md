# Nodal current injection as branch currents plus shunt current

For a real `n_N × n_E` matrix `B`, complex node voltages `V_v`, complex branch admittances `y_e` and
complex shunt admittances `y^s_v`, the
[current injected at node](../ac-power-injections-and-network-losses/node-injection.md) `v` is

`∑_e B_{ve} I_e + y^s_v V_v`,

where `I_e = y_e ∑_u B_{ue} V_u` is the [branch current](branch-current.md).
