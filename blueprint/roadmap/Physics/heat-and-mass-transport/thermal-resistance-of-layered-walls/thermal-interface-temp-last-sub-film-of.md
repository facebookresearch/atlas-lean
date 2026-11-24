# For positive data the reconstruction ends at the outside temperature

Let `A`, `h_in` and `h_out` be positive, and `L i ≥ 0` and `k i > 0` for every `i < n`. Then the
[total resistance](thermal-series-resistance.md)
`R = 1/(h_in A) + ∑_{i < n} L i/(k i A) + 1/(h_out A)` is positive, and with the heat rate
`Q = (T_in - T_out)/R` the [interface temperature](thermal-interface-temp.md)
`T_m = T_in - Q (1/(h_in A) + ∑_{i < m} L i/(k i A))` satisfies

`T_n - Q/(h_out A) = T_out`.
