# In counterflow, the hot stream loses what the cold stream gains

Let `(T_h, T_c)` be a [counterflow solution](is-counterflow-solution.md) on `[0, L]` for real `C_h`,
`C_c`, `K`, `L`, `T_hi`, `T_ci`. Then for every `x ∈ [0, L]`,

`C_h (T_hi - T_h(x)) = C_c (T_c(0) - T_c(x))`;

at `x = L` this is the port balance `C_h (T_hi - T_h(L)) = C_c (T_c(0) - T_ci)`. No sign condition
is needed.
