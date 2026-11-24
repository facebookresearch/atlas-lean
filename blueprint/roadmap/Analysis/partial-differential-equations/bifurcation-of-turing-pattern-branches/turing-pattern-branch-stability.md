# Supercritical Turing pattern branches are stable

Combine `turing_patternBranch` with
`patternBranch_direction_stability`: for an admissible mode `k` (e.g. a Neumann mode `k_n`) at
its neutral diffusion `d₀`, a reduced map `G` (strictly differentiable, equal to the critical
eigenvalue on the trivial branch, reflection-symmetric to second order with coefficient
`c = H(0, d₀) ≠ 0`) has a local pattern branch `d = φ(a)` through `(0, d₀)` which, for small
amplitudes `a ≠ 0`, lies on the side `c (φ(a) - d₀) < 0` and has reduced linearization `λ` with
`0 < c λ`. In particular, if `c < 0` the branch exists for `d > d₀`, where the critical
eigenvalue of mode `k` is positive, and is linearly stable in the reduced equation. As in
`turing_patternBranch`, other Neumann modes are not controlled, so this says nothing about the
stability of the homogeneous state on `[0, L]` for `d < d₀`, nor of the branch in the full PDE.
