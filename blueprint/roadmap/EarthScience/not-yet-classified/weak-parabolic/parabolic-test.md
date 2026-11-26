# Test functions

The test functions of the parabolic weak formulation are the smooth
functions on time × space whose support, the closure of the set where they do not vanish, lies
inside the open rectangle `(t0, t1) × (0, 1)`. Such a support is closed and bounded, hence
compact.
Note: `ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞)` is C^∞. Under current Mathlib `ContDiff` is indexed
by `ℕ∞ω`, where `⊤ = ω` means analytic, while `∞` means C^∞.
