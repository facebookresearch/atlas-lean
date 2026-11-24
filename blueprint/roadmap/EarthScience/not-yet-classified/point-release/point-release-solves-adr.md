# Point release solves adr

The point-release kernel
`c(t, x) = M exp(-k t) exp(-(x - U t)² / (4 D t)) / √(4 π D t)` solves the
advection-diffusion-reaction equation `c_t + U c_x = D c_xx - k c` for `t > 0`
and every real `k` (derivatives written with `deriv`, with the other variable
held fixed). The reaction is decay only when `k ≥ 0`. The derivatives exist:
see `point_release_hasDerivAt_t`, `point_release_hasDerivAt_x` and
`point_release_hasDerivAt_xx`.
