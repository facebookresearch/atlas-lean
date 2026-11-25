/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.BSDE
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Wanted: well-posedness, comparison and the nonlinear Feynman–Kac formula for BSDEs

The three basic theorems of the theory of backward stochastic differential equations, as surveyed
by S. Peng, *Backward stochastic differential equation, nonlinear expectation and their
applications*, Proc. ICM 2010 (Hyderabad), Vol. I, §§1.2–1.3, stated for a one-dimensional
Brownian motion and one-dimensional `Y` (`d = m = n = 1`) with the solution notion
`MathlibExt.Probability.BSDE.IsBSDESolution`:

* `bsde_existsUnique`: existence and uniqueness for Lipschitz generators (Pardoux and Peng,
  1990; Theorem 1.1 there);
* `bsde_comparison`: the comparison theorem (Peng, 1992; El Karoui, Peng and Quenez, 1997;
  Theorem 1.2 there);
* `bsde_feynmanKac_of_classical`: the nonlinear Feynman–Kac formula `Y_t = u(t, X_t)` when the
  quasilinear PDE has a classical solution (Peng, 1991; Theorem 1.3 there and the paragraph after
  it).

## References

* S. Peng, *Backward stochastic differential equation, nonlinear expectation and their
  applications*, Proceedings of the International Congress of Mathematicians 2010, Vol. I,
  pp. 393–432, Hindustan Book Agency, 2010.
* E. Pardoux and S. Peng, *Adapted solution of a backward stochastic differential equation*,
  Systems Control Lett. 14 (1990), 55–61.
* N. El Karoui, S. Peng and M.-C. Quenez, *Backward stochastic differential equations in
  finance*, Math. Finance 7 (1997), 1–71.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.BSDE
open scoped NNReal ENNReal

namespace MathlibExt.Probability.BSDEWanted

/-- **Existence and uniqueness for BSDEs with Lipschitz generators** (Pardoux–Peng 1990). Let `B`
be a real Brownian motion with continuous paths and `F` its augmented filtration. Let the
generator `g(t, ω, y, z)` be progressive in `(t, ω)` with `E ∫_0^T g(t, y, z)² dt < ∞` for each
`(y, z)`, and Lipschitz in `(y, z)`: `|g(t, y, z) - g(t, y', z')| ≤ μ (|y - y'| + |z - z'|)`.
Then for every `F_T`-measurable square-integrable `ξ` the BSDE `Y_t = ξ + ∫_t^T g(s, Y_s, Z_s) ds -
∫_t^T Z_s dB_s` has a solution `(Y, Z)` in `M²(0, T)` whose `Y` has almost surely continuous paths
on `[0, T]`, and two solutions agree in `M²(0, T)`. This is the case `d = m = 1` of
S. Peng, Proc. ICM 2010, Vol. I, Theorem 1.1 (E. Pardoux and S. Peng, Systems Control Lett. 14
(1990)). -/
theorem_wanted bsde_existsUnique {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBcont : ∀ ω, Continuous fun t ↦ B t ω)
    (hF : IsAugmentedBrownianFiltration P F B) {T : ℝ≥0} {g : ℝ≥0 → Ω → ℝ → ℝ → ℝ}
    (hg_prog : ∀ y z, IsProgressive F fun t ω ↦ g t ω y z)
    (hg_sq : ∀ y z, ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) T, ‖g u.toNNReal ω y z‖ₑ ^ 2) ∂P ≠ ∞)
    {μ : ℝ} (hg_lip : ∀ t ω y y' z z', |g t ω y z - g t ω y' z'| ≤ μ * (|y - y'| + |z - z'|))
    {ξ : Ω → ℝ} (hξm : Measurable[F T] ξ) (hξ : MemLp ξ 2 P) :
    (∃ Y Z : ℝ≥0 → Ω → ℝ, IsBSDESolution P F B T g ξ Y Z ∧
        ∀ᵐ ω ∂P, ContinuousOn (fun t ↦ Y t ω) (Set.Iic T)) ∧
      ∀ Y Z Y' Z' : ℝ≥0 → Ω → ℝ, IsBSDESolution P F B T g ξ Y Z →
        IsBSDESolution P F B T g ξ Y' Z' →
        ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) T, ‖Y u.toNNReal ω - Y' u.toNNReal ω‖ₑ ^ 2 +
          ‖Z u.toNNReal ω - Z' u.toNNReal ω‖ₑ ^ 2) ∂P = 0

/-- **Comparison theorem for one-dimensional BSDEs** (Peng 1992; El Karoui–Peng–Quenez 1997). Under
the hypotheses of `bsde_existsUnique` on two generators `g₁, g₂` and two terminal values
`ξ₁, ξ₂`, if `ξ₁ ≥ ξ₂` almost surely and, for each `(t, y, z)`, `g₁(t, y, z) ≥ g₂(t, y, z)`
almost surely, then the solutions satisfy `Y¹_t ≥ Y²_t` almost surely for every `t ∈ [0, T]`.
S. Peng, Proc. ICM 2010, Vol. I, Theorem 1.2. -/
theorem_wanted bsde_comparison {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBcont : ∀ ω, Continuous fun t ↦ B t ω)
    (hF : IsAugmentedBrownianFiltration P F B) {T : ℝ≥0} {g₁ g₂ : ℝ≥0 → Ω → ℝ → ℝ → ℝ}
    (hg₁_prog : ∀ y z, IsProgressive F fun t ω ↦ g₁ t ω y z)
    (hg₂_prog : ∀ y z, IsProgressive F fun t ω ↦ g₂ t ω y z)
    (hg₁_sq : ∀ y z, ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) T, ‖g₁ u.toNNReal ω y z‖ₑ ^ 2) ∂P ≠ ∞)
    (hg₂_sq : ∀ y z, ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) T, ‖g₂ u.toNNReal ω y z‖ₑ ^ 2) ∂P ≠ ∞)
    {μ : ℝ} (hg₁_lip : ∀ t ω y y' z z', |g₁ t ω y z - g₁ t ω y' z'| ≤ μ * (|y - y'| + |z - z'|))
    (hg₂_lip : ∀ t ω y y' z z', |g₂ t ω y z - g₂ t ω y' z'| ≤ μ * (|y - y'| + |z - z'|))
    {ξ₁ ξ₂ : Ω → ℝ} (hξ₁m : Measurable[F T] ξ₁) (hξ₁ : MemLp ξ₁ 2 P)
    (hξ₂m : Measurable[F T] ξ₂) (hξ₂ : MemLp ξ₂ 2 P) (hξ : ∀ᵐ ω ∂P, ξ₂ ω ≤ ξ₁ ω)
    (hg : ∀ t y z, ∀ᵐ ω ∂P, g₂ t ω y z ≤ g₁ t ω y z) {Y₁ Z₁ Y₂ Z₂ : ℝ≥0 → Ω → ℝ}
    (h₁ : IsBSDESolution P F B T g₁ ξ₁ Y₁ Z₁) (h₂ : IsBSDESolution P F B T g₂ ξ₂ Y₂ Z₂) :
    ∀ t ≤ T, ∀ᵐ ω ∂P, Y₂ t ω ≤ Y₁ t ω

/-- **Nonlinear Feynman–Kac formula, classical case** (Peng 1991; Pardoux–Peng 1992). Let
`b, σ, φ : ℝ → ℝ` be Lipschitz, `f(x, y, z)` Lipschitz on `ℝ³`, and let `X` solve the SDE
`X_t = x + ∫_0^t σ(X_s) dB_s + ∫_0^t b(X_s) ds` (in the solution class of
`MathlibExt.Probability.LipschitzSDEWanted.sde_lipschitz_existsUnique`). Suppose that
`u(t, x)` is `C²` with bounded `∂ₓu` and linear growth, and solves the quasilinear parabolic PDE
`∂ₜu + b ∂ₓu + ½ σ² ∂ₓ²u + f(x, u, σ ∂ₓu) = 0` on `[0, T] × ℝ` with `u(T, ·) = φ`. Then every
solution `(Y, Z)` of the Markovian BSDE with generator `f(X_t, y, z)` and terminal value
`φ(X_T)` satisfies `Y_t = u(t, X_t)` almost surely for each `t ∈ [0, T]`; in particular
`Y_0 = u(0, x)`. S. Peng, Proc. ICM 2010, Vol. I, Theorem 1.3 (stated there for the viscosity
solution) and the paragraph after it, which records Peng's (1991) proof when the PDE (1.11) has a
classical solution. -/
theorem_wanted bsde_feynmanKac_of_classical {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBcont : ∀ ω, Continuous fun t ↦ B t ω)
    (hF : IsAugmentedBrownianFiltration P F B) {b σ φ : ℝ → ℝ} {K : ℝ≥0}
    (hb : LipschitzWith K b) (hσ : LipschitzWith K σ) (hφ : LipschitzWith K φ)
    {f : ℝ → ℝ → ℝ → ℝ} {μ : ℝ}
    (hf : ∀ x x' y y' z z', |f x y z - f x' y' z'| ≤ μ * (|x - x'| + |y - y'| + |z - z'|))
    {T : ℝ≥0} {x : ℝ} {X : ℝ≥0 → Ω → ℝ} (hXF : Adapted F X)
    (hXcont : ∀ ω, Continuous fun t ↦ X t ω)
    (hX2 : ∀ t : ℝ≥0, ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖X u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞)
    (hX : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X t ω = x + itoIntegral P F B (fun u ω ↦ σ (X u ω)) t ω +
      ∫ u in (0 : ℝ)..t, b (X u.toNNReal ω))
    {u : ℝ → ℝ → ℝ} (hu : ContDiff ℝ 2 fun p : ℝ × ℝ ↦ u p.1 p.2)
    (hux : ∃ C : ℝ, ∀ t y, |deriv (u t) y| ≤ C) (hgrowth : ∃ C : ℝ, ∀ t y, |u t y| ≤ C * (1 + |y|))
    (hpde : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ y, deriv (fun s ↦ u s y) t + b y * deriv (u t) y +
      σ y ^ 2 / 2 * deriv (deriv (u t)) y + f y (u t y) (σ y * deriv (u t) y) = 0)
    (hterm : ∀ y, u T y = φ y) {Y Z : ℝ≥0 → Ω → ℝ}
    (hYZ : IsBSDESolution P F B T (fun t ω y z ↦ f (X t ω) y z) (fun ω ↦ φ (X T ω)) Y Z) :
    ∀ t ≤ T, ∀ᵐ ω ∂P, Y t ω = u t (X t ω)

end MathlibExt.Probability.BSDEWanted
