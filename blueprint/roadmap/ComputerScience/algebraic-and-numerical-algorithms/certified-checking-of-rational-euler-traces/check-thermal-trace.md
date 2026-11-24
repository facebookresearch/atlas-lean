# The trace checker

Accept a list `y` of rationals exactly when it has eleven entries
`y_0, …, y_10`, the first is the initial coefficient `y_0 = 1`, and all ten identities
`y_(j+1) = (9 / 10) y_j`, `j = 0, …, 9`, hold. The entries are the coefficients of
`T_j = T_amb + Δ y_j`, the normalized excesses `(T_j - T_amb) / Δ` only for `Δ ≠ 0`. Entries are
read with the default `0`, which an accepted list never uses. The certificate is the
eleven-element list itself, `y_10` included; there is no separately supplied expected terminal
value or error bound.
