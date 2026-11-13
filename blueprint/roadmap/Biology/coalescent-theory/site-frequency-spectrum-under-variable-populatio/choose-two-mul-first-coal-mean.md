# Closed form of the first-coalescence times

For a history with `K ≥ 1` pieces and
`m ≥ 2`, writing `a = C(m,2)` and `R = cumRate h.sizeFn`,
`a c_m = size 0 + ∑_{j=1}^{K-1} (size j - size (j-1)) exp(-a R(start j))`. In particular the
integral defining `c_m` converges.
