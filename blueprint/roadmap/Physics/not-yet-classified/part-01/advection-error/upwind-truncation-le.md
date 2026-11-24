# Upwind truncation le

Nodal truncation error of the upwind update on the point samples: with `dx = L / ncells`,
Courant number `ν = v * dt / dx ≥ 0` and `M = |a| (2π / L)²`, at every node, the wrapped one
included, `|w_j^(n+1) - ((1 - ν) w_j^n + ν w_(j-1)^n)| ≤ dt * M * (v² dt + v dx) / 2`.
