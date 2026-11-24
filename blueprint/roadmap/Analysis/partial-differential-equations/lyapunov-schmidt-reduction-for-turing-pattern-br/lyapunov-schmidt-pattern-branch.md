# Pattern branches of the full problem from the reduced branch theorem

Let `F(x, d)` have
the trivial branch `F(0, d) = 0` near `d₀` and a linearization at `(0, d₀)` with one-dimensional
kernel `ker L = ℝ φ` (`φ ≠ 0`) and `range L = ker ψ` for a functional `ψ` (Fredholm package
hypotheses as in `lyapunovSchmidt_scalar`). Assume the scalar
bifurcation function factors as `G̃(a, d) = a G(a, d)` near `(0, d₀)` with `G` strictly
differentiable, `G(0, d₀) = 0` and `∂_d G(0, d₀) ≠ 0`.

The reduced Crandall–Rabinowitz branch theorem for `a G(a, d) = 0`, specialized to this `G`, is
the explicit hypothesis `hCR`; the universal `exists_patternBranch` of
`Domains.Biology.Dynamics.TuringBranches` (PR #1533, not yet merged) specializes to it at the
call site (`hCR := exists_patternBranch`). Then the full equation has a unique local pattern
branch: a `d = β(a)` through `(0, d₀)` with slope `-∂_a G / ∂_d G` such that near `(0, d₀)` the
solutions of `F(x, d) = 0` are exactly the trivial ones `x = 0` and the branch
`x = a φ + W(a φ, d)`, `d = β(a)`; every point of the branch solves `F = 0` for small `a`.
