# Gotoh continuation value after a gap in the second sequence

Fix an integer-valued
scoring function $\sigma$ on pairs of letters and integer gap-open and gap-extend penalties $g_o$
and $g_e$. For sequences $u$ and $v$, the value $X(u, v)$ is the fuel-bounded Gotoh recursion on
$u$ and $v$, run with fuel equal to the sum of their lengths and started in the gap state where
the previous column was a gap in $v$.

It is the best affine-gap score of an alignment of $u$ with $v$ scored from that state. It is a
continuation value, not an endpoint-restricted matrix: the next column may be a match or either
gap, and the previous state only makes a next gap in $v$ cost $g_e$ instead of $g_o$.
