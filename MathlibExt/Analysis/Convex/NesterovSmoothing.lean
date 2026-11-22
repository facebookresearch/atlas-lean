/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# Nesterov's smoothing of max-type functions

For a linear operator `A : E → F`, a set `Q ⊆ F`, a function `φ` on `Q` and a prox-function `d`
on `Q`, the function `f₀(x) = max_{u ∈ Q} (⟪A x, u⟫ - φ(u))` is approximated by
`f_μ(x) = max_{u ∈ Q} (⟪A x, u⟫ - φ(u) - μ d(u))`, after Yu. Nesterov, *Smooth minimization of
non-smooth functions*, Math. Program. 103 (2005) 127-152, Section 2, (2.5). The source works in
finite-dimensional normed spaces with dual norms; here `E` and `F` are real inner product spaces.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.NesterovSmoothing

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Nesterov's smoothed max-type function.** For `A : E →L[ℝ] F`, `Q ⊆ F`, `φ d : F → ℝ` and
`μ ≥ 0`, `smoothedMax A φ d Q μ x = sup_{u ∈ Q} (⟪A x, u⟫ - φ(u) - μ d(u))`; with `μ = 0` it is the
max-type function `f₀` itself. This is (2.5) of Yu. Nesterov, *Smooth minimization of non-smooth
functions*, Math. Program. 103 (2005) 127-152, where `Q = Q₂` is bounded closed convex, `φ = φ̂`
is continuous and convex and `d = d₂` is a prox-function of `Q₂`, so that the maximum is attained.
As a supremum in `ℝ` it is meaningful only when the set of values is bounded above (for instance
`Q` compact with continuous `φ` and `d`), and it is `0` for empty `Q`. -/
noncomputable def smoothedMax (A : E →L[ℝ] F) (φ d : F → ℝ) (Q : Set F) (μ : ℝ) (x : E) : ℝ :=
  sSup ((fun u => inner ℝ (A x) u - φ u - μ * d u) '' Q)

/-- **Uniform approximation by the smoothed function.** Let `Q ⊆ F` be compact and nonempty,
`φ` and `d` continuous on `Q` with `d ≥ 0` on `Q`, and `μ ≥ 0`, and put `D = sup_{u ∈ Q} d(u)`.
Then for every `x`, `f_μ(x) ≤ f₀(x) ≤ f_μ(x) + μ D`, where `f_μ = smoothedMax A φ d Q μ`.

This is (2.7) of Yu. Nesterov, *Smooth minimization of non-smooth functions*, Math. Program. 103
(2005) 127-152, where `d₂ ≥ 0` on `Q₂` because the prox-function is normalised by
`d₂(u₀) = min_{Q₂} d₂ = 0`; only `d ≥ 0` on `Q` is assumed here. -/
theorem smoothedMax_le_and_le (A : E →L[ℝ] F) {φ d : F → ℝ} {Q : Set F} (hQ : IsCompact Q)
    (hQne : Q.Nonempty) (hφ : ContinuousOn φ Q) (hd : ContinuousOn d Q)
    (hd0 : ∀ u ∈ Q, 0 ≤ d u) {μ : ℝ} (hμ : 0 ≤ μ) (x : E) :
    smoothedMax A φ d Q μ x ≤ smoothedMax A φ d Q 0 x ∧
      smoothedMax A φ d Q 0 x ≤ smoothedMax A φ d Q μ x + μ * sSup (d '' Q) := by
  have hcont : ∀ ν : ℝ, ContinuousOn (fun u => inner ℝ (A x) u - φ u - ν * d u) Q := fun ν =>
    ((continuous_const.inner continuous_id).continuousOn.sub hφ).sub
      (continuousOn_const.mul hd)
  have hbdd : ∀ ν : ℝ, BddAbove ((fun u => inner ℝ (A x) u - φ u - ν * d u) '' Q) := fun ν =>
    hQ.bddAbove_image (hcont ν)
  have hbddD : BddAbove (d '' Q) := hQ.bddAbove_image hd
  refine ⟨?_, ?_⟩
  · refine csSup_le (hQne.image _) ?_
    rintro _ ⟨u, hu, rfl⟩
    have h1 : inner ℝ (A x) u - φ u - 0 * d u ≤ smoothedMax A φ d Q 0 x :=
      le_csSup (hbdd 0) ⟨u, hu, rfl⟩
    have h2 : 0 ≤ μ * d u := mul_nonneg hμ (hd0 u hu)
    simp only at h1 ⊢
    linarith
  · refine csSup_le (hQne.image _) ?_
    rintro _ ⟨u, hu, rfl⟩
    have h1 : inner ℝ (A x) u - φ u - μ * d u ≤ smoothedMax A φ d Q μ x :=
      le_csSup (hbdd μ) ⟨u, hu, rfl⟩
    have h2 : d u ≤ sSup (d '' Q) := le_csSup hbddD ⟨u, hu, rfl⟩
    have h3 := mul_le_mul_of_nonneg_left h2 hμ
    simp only
    linarith

end MathlibExt.Analysis.Convex.NesterovSmoothing
