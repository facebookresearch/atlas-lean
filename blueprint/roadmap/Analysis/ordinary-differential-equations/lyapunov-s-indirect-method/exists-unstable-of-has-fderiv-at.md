# Lyapunov's indirect method, instability

**Lyapunov's indirect method, instability** (Khalil 2002, Theorem 4.7). If `f` is `C¹`,
`f x⋆ = 0`, and the Jacobian matrix `A` of `f` at `x⋆` has an eigenvalue with positive real
part, then `x⋆` is unstable: for some `ε > 0`, every neighbourhood of `x⋆` contains an initial
point `x₀` from which a solution segment of `x' = f(x)` on some finite interval `[0, T]`
reaches distance `≥ ε` from `x⋆`. Quantifying over finite segments (rather than only over
solutions on all of `[0, ∞)`) keeps the statement non-vacuous when solutions blow up in
finite time.
