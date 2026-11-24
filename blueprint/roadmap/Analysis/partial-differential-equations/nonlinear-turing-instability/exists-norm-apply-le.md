# Bounded orbits on a stable mode

If `S` acts on the Neumann mode `n` through the modal ODE
of a stable matrix `M` (`tr M < 0 < det M`), the orbits of that mode stay bounded:
`‖S t (cos(k_n ·) w)‖ ≤ C ‖w‖` for all `t ≥ 0`. The proof uses the Lyapunov function
`V(c) = det M (c₀² + c₁²) + (M c)₀² + (M c)₁²`, which satisfies
`V' = 2 tr M ((M c)₀² + (M c)₁²) ≤ 0` along `c' = M c` (Cayley–Hamilton).
