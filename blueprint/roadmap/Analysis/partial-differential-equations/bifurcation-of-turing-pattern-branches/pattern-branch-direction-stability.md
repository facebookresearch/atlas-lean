# Direction and stability of the pattern branch (pitchfork)

Suppose the reduced map is
symmetric to second order, `G(a, d) = G(0, d) + a² H(a, d)` near `(0, d₀)` (for every critical
mode `n ≥ 1` the quadratic term of the reaction projects to zero on `cos(k_n x)` because
`∫₀ᴸ cos³(k_n x) dx = 0`, so `G` has no term linear in `a`; for odd `n` the reflection
`x ↦ L - x` even makes `G` even in `a`), with `H` continuous at `(0, d₀)`, `c = H(0, d₀) ≠ 0`,
and `H` differentiable in `a` with partial derivative `H_a` continuous at `(0, d₀)`. Let the
trivial branch cross transversally, `∂_d G(0, d₀) = σ > 0`, and let `φ` be the pattern branch of
`exists_patternBranch`. Then for small `a ≠ 0`:

* `c (φ(a) - d₀) < 0`: the branch bifurcates *supercritically* (into `d > d₀`, where the trivial
  equilibrium of the reduced equation is unstable, `G(0, d) > 0`) iff `c < 0`, and
  subcritically iff `c > 0`;
* the branch equilibrium `a` of the reduced equation `ȧ = Φ(a, d) = a G(a, d)` at `d = φ(a)` has
  linearization `λ = ∂_a Φ(a, φ(a))` with `0 < c λ`: it is linearly stable (`λ < 0`) iff the
  bifurcation is supercritical (exchange of stability within the reduced equation).
