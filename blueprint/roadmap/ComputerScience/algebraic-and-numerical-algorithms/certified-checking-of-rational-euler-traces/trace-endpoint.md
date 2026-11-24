# Endpoint temperature reconstructed from a trace

For real numbers `T_amb` (bath temperature) and `Δ` (initial excess `T_0 - T_amb`) and a list `y` of
rationals, the reconstructed endpoint is `T_amb + Δ y_10`, where `y_10` is the entry at index `10`
(`0` when the list is shorter). For `Δ = 0` the endpoint is `T_amb` for every list.
