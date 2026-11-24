# Truncation error of the upwind update on the sampled wave

For real numbers `L > 0`, `Δt > 0`, `c₀`, `a` and `v`, a number of cells `N_c ≥ 1` with Courant
number `ν = v Δt / Δx ≥ 0` (`Δx = L / N_c`), every time level `n` and every node `j`, the
[samples](sampled-wave.md) `w` satisfy
`|w_j^{n+1} - ((1 - ν) w_j^n + ν w_{j-1}^n)| ≤ Δt M (v² Δt + v Δx) / 2` with `M = |a| (2π / L)²`,
including the wrapped node `j = 0`.
