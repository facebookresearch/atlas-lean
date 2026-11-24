# Turing pattern branch and sign change of the selected critical eigenvalue

Let mode `k`
be admissible (`0 < f_u k² - d_u k⁴`) with neutral diffusion `d₀ = d_n(k²)` and negative trace
there, and let `G` be a reduced bifurcation map for this mode: strictly differentiable at
`(0, d₀)` and equal on the trivial branch to the critical eigenvalue,
`G (0, d) = leadingEigenvalue (J - k² D(d))` for `d` near `d₀` (the output of a Lyapunov–Schmidt
reduction, assumed). Then the crossing is transversal (`0 < ∂_d G (0, d₀)`), a unique local
pattern branch `d = φ(a)` bifurcates from `(0, d₀)`, and the critical eigenvalue of mode `k`
changes sign there: `G (0, d)` is negative for `d < d₀` and positive for `d > d₀` near `d₀`.

Only mode `k` is controlled. The hypotheses say nothing about the other Neumann modes, so this is
not an exchange of stability of the homogeneous state on `[0, L]`: another mode may already be
unstable at `d₀` (for `J₀`, `d_u = 1`, `k = 1/2` on `[0, 8π]`, mode `4` is neutral while mode
`5` is unstable; see the tests). That stronger conclusion would need every other Neumann mode
to be stable near `d₀`.
