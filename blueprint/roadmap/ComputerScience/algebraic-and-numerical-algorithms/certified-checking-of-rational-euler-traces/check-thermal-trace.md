# Checker for a trace of Euler cooling coefficients

For a list `y` of rational numbers, the checker returns true exactly when `y` has eleven entries
`y_0, …, y_10`, `y_0 = 1`, and `y_{j+1} = (9/10) y_j` for `j = 0, …, 9`. Entries are read with the
default `0` beyond the end of the list, which an accepted list never uses. The entries are meant as
the coefficients of the temperatures `T_j = T_amb + Δ y_j` of ten explicit Euler steps of a body
cooling in a bath; they are the normalised excesses `(T_j - T_amb) / Δ` only when `Δ ≠ 0`.
