# Specific Entropy Change

The entropy change per unit mass of a calorically perfect gas from the state `(T1, v1)` to the
state `(T2, v2)`: `cv log (T2 / T1) + R log (v2 / v1)`, with the specific heat at constant volume
`cv`, the specific gas constant `R` and the specific volumes `v1`, `v2` (`v = 1 / ρ`). Domain:
positive temperatures and specific volumes; elsewhere `Real.log` returns a junk value.
