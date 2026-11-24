# At one time, the zone heat inventory changes at the external power

Let `ι` be a finite set of zones, with capacities `C : ι → ℝ`, conductances `G : ι × ι → ℝ` with
`G_{ij} = G_{ji}` for all zones, and temperatures `T_i`, rates `v_i`, boundary inputs `b_i` and
heating powers `P_i`, all real functions of time. Fix a time `t` at which, for every zone `i`, `T_i`
has derivative `v_i(t)` and the zone equation

`C_i v_i(t) = ∑_j G_{ij} (T_j(t) - T_i(t)) + b_i(t) + P_i(t)`

holds. Then the total heat inventory `s ↦ ∑_i C_i T_i(s)` has derivative `∑_i (b_i(t) + P_i(t))`
at `t`: internal exchange cancels by reciprocity. Only data at the time `t` is used; no sign
condition on the capacities or conductances is needed.
