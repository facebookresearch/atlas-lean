# Isoperimetric

The generalized isoperimetric constant `η(G, m)` of Ganesh, Massoulié and Towsley (2005,
Eq. (4)): defined via `sInf` of `E(S, Sᶜ) / |S|` over nonempty vertex sets `S` with `|S| ≤ m`.
When `V` is nonempty and `1 ≤ m`, this finite nonempty set attains its minimum; when no admissible
subset exists (for example `m = 0`), Lean's real infimum convention `sInf ∅ = 0` yields `0`.
