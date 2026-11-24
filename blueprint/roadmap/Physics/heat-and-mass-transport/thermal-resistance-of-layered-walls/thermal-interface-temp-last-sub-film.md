# For R ≠ 0 the reconstruction ends at the outside air temperature

Let `n` be a natural number and `A`, `h_in`, `h_out`, `T_in`, `T_out` reals and `L`, `k` sequences,
and let the [total resistance](thermal-series-resistance.md)
`R = 1/(h_in A) + ∑_{i < n} L i/(k i A) + 1/(h_out A)` be nonzero. With the heat rate
`Q = (T_in - T_out)/R`, the [interface temperature](thermal-interface-temp.md)
`T_m = T_in - Q (1/(h_in A) + ∑_{i < m} L i/(k i A))` satisfies

`T_n - Q/(h_out A) = T_out`:

the last interface minus the outside film drop is the outside air temperature.
