# Sideal EOS fails at N zero

Boundary countermodel, equation-of-state failure: at `(U, V, N) = (1, 1, 0)` with
`kB = 1`, every hypothesis of `sideal_U` except `0 < N` holds, and its conclusion
`U = (3/2) * N * kB * T` fails, so `0 < N` cannot be dropped from `sideal_U`.
