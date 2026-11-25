/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.InnerProductSpace.Adjoint
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

-- Take the strong concavity inequality along the segment out of the maximizer, divide by the
-- positive weight of the second point, and then let that weight tend to zero.
private theorem quadratic_gap_of_isMaxOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Q : Set V} {g : V → ℝ} {m : ℝ} (hg : StrongConcaveOn Q m g) {u v : V}
    (hu : u ∈ Q) (hv : v ∈ Q) (hmax : IsMaxOn g Q u) :
    g v + m / 2 * ‖u - v‖ ^ 2 ≤ g u := by
  have h0 : (0 : ℝ) ∈ closure (Set.Ioo 0 1) := by
    rw [closure_Ioo zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩
  have hcont : Continuous (fun t : ℝ => g v + (1 - t) * (m / 2 * ‖u - v‖ ^ 2)) := by
    fun_prop
  suffices h : g v + (1 - (0 : ℝ)) * (m / 2 * ‖u - v‖ ^ 2) ≤ g u by simpa using h
  refine ContinuousWithinAt.closure_le h0 hcont.continuousWithinAt continuousWithinAt_const ?_
  intro t ht
  have ht' : 0 < t := ht.1
  have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2.le
  have hab : 1 - t + t = 1 := by ring
  have hseg := hg.2 hu hv ht1 ht'.le hab
  have hbound : g ((1 - t) • u + t • v) ≤ g u := hmax (hg.1 hu hv ht1 ht'.le hab)
  simp only [smul_eq_mul] at hseg
  apply le_of_mul_le_mul_left _ ht'
  linarith only [hseg, hbound]

/-- **The smoothed max-type function has a Lipschitz gradient.** Let `E`, `F` be
finite-dimensional real inner product spaces, `A : E →L[ℝ] F`, `Q ⊆ F` nonempty, compact and
convex, `φ` continuous and convex on `Q`, `d` continuous and `σ`-strongly convex on `Q` with
`σ > 0`, and `μ > 0`. Then `f_μ = smoothedMax A φ d Q μ` is convex and differentiable on `E`,
and its gradient is Lipschitz with constant `‖A‖ ^ 2 / (μ σ)`.

This is [Theorem 1](https://doi.org/10.1007/s10107-004-0552-5) of Yu. Nesterov,
*Smooth minimization of nonsmooth functions*, Math. Program. 103 (2005) 127–152, specialised to
Euclidean norms on both spaces, for which the norm `‖A‖_{1,2}` of the source is the operator norm.
The source also states the gradient formula `∇f_μ(x) = A* u_μ(x)`, with `u_μ(x)` the unique
maximiser. -/
theorem smoothedMax_convex_differentiable_lipschitz {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (A : E →L[ℝ] F) {φ d : F → ℝ} {Q : Set F} (hQ : IsCompact Q) (hQne : Q.Nonempty)
    (hQc : Convex ℝ Q) (hφ : ContinuousOn φ Q) (hφc : ConvexOn ℝ Q φ) (hd : ContinuousOn d Q)
    {σ : ℝ} (hσ : 0 < σ) (hdσ : StrongConvexOn Q σ d) {μ : ℝ} (hμ : 0 < μ) :
    ConvexOn ℝ Set.univ (smoothedMax A φ d Q μ) ∧ Differentiable ℝ (smoothedMax A φ d Q μ) ∧
      LipschitzWith ⟨‖A‖ ^ 2 / (μ * σ), div_nonneg (sq_nonneg _) (mul_pos hμ hσ).le⟩
        (gradient (smoothedMax A φ d Q μ)) := by
  let g (x : E) (v : F) := inner ℝ (A x) v - φ v - μ * d v
  let f := smoothedMax A φ d Q μ
  have hcont (x : E) : ContinuousOn (g x) Q :=
    ((continuous_const.inner continuous_id).continuousOn.sub hφ).sub (continuousOn_const.mul hd)
  have hmax (x : E) : ∃ v ∈ Q, IsMaxOn (g x) Q v := hQ.exists_isMaxOn hQne (hcont x)
  choose u hu hopt using hmax
  have hle (x : E) {v : F} (hv : v ∈ Q) : g x v ≤ f x :=
    le_csSup (hQ.bddAbove_image (hcont x)) ⟨v, hv, rfl⟩
  have hval (x : E) : f x = g x (u x) := by
    refine le_antisymm (csSup_le (hQne.image (g x)) ?_) (hle x (hu x))
    rintro _ ⟨v, hv, rfl⟩
    exact hopt x hv
  have hdiff (x y : E) (v : F) : g x v - g y v = inner ℝ (A (x - y)) v := by
    simp only [g, map_sub, inner_sub_left]
    ring
  have hconv : ConvexOn ℝ Set.univ f := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    let v := u (a • x + b • y)
    calc
      f (a • x + b • y) = g (a • x + b • y) v := hval _
      _ = a * g x v + b * g y v := by
        simp only [g, map_add, map_smul, inner_add_left, real_inner_smul_left]
        linear_combination (φ v + μ * d v) * hab
      _ ≤ a • f x + b • f y :=
        add_le_add (mul_le_mul_of_nonneg_left (hle x (hu _)) ha)
          (mul_le_mul_of_nonneg_left (hle y (hu _)) hb)
  have hstrong (x : E) : StrongConcaveOn Q (μ * σ) (g x) := by
    refine ⟨hQc, fun v hv w hw a b ha hb hab => ?_⟩
    have hφ' := hφc.2 hv hw ha hb hab
    have hd' := mul_le_mul_of_nonneg_left (hdσ.2 hv hw ha hb hab) hμ.le
    simp only [smul_eq_mul] at hφ' hd'
    simp only [g, smul_eq_mul, inner_add_right, real_inner_smul_right]
    linear_combination hφ' + hd'
  have hinner (v : E) (w : F) : inner ℝ (A v) w ≤ ‖A‖ * ‖v‖ * ‖w‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (A.le_opNorm v) (norm_nonneg _))
  have hμσ : 0 < μ * σ := mul_pos hμ hσ
  -- Adding the two optimality gaps bounds the change in the maximizer without differentiating
  -- either penalty on Q.
  have hu_le (x y : E) : ‖u x - u y‖ ≤ ‖A‖ / (μ * σ) * ‖x - y‖ := by
    have hx := quadratic_gap_of_isMaxOn (hstrong x) (hu x) (hu y) (hopt x)
    have hy := quadratic_gap_of_isMaxOn (hstrong y) (hu y) (hu x) (hopt y)
    rw [norm_sub_rev (u y) (u x)] at hy
    have hpair : μ * σ * ‖u x - u y‖ ^ 2 ≤ inner ℝ (A (x - y)) (u x - u y) := calc
      _ ≤ (g x (u x) - g y (u x)) - (g x (u y) - g y (u y)) := by linarith only [hx, hy]
      _ = _ := by rw [hdiff, hdiff, inner_sub_right]
    rcases (norm_nonneg (u x - u y)).eq_or_lt with hzero | hpos
    · rw [← hzero]
      positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hμσ]
    apply le_of_mul_le_mul_right _ hpos
    calc
      _ = μ * σ * ‖u x - u y‖ ^ 2 := by ring
      _ ≤ ‖A‖ * ‖x - y‖ * ‖u x - u y‖ := hpair.trans (hinner _ _)
  -- Evaluate at the two maximizers to sandwich the error of the candidate linearization.
  have hgrad (x : E) : HasGradientAt f (A.adjoint (u x)) x := by
    rw [hasGradientAt_iff_isLittleO_nhds_zero]
    refine (Asymptotics.isBigO_of_le' (c := ‖A‖ ^ 2 / (μ * σ)) _ ?_).trans_isLittleO
      (Asymptotics.isLittleO_norm_pow_id (by decide : 1 < 2))
    intro v
    rw [Real.norm_of_nonneg (sq_nonneg ‖v‖), A.adjoint_inner_left, real_inner_comm (A v) (u x)]
    have hshift (w : F) : g (x + v) w - g x w = inner ℝ (A v) w := by
      rw [hdiff, add_sub_cancel_left]
    have hlo : 0 ≤ f (x + v) - f x - inner ℝ (A v) (u x) := by
      linarith only [hle (x + v) (hu x), hval x, hshift (u x)]
    rw [Real.norm_of_nonneg hlo]
    calc
      _ ≤ inner ℝ (A v) (u (x + v) - u x) := by
        rw [inner_sub_right]
        linarith only [hle x (hu (x + v)), hval (x + v), hshift (u (x + v))]
      _ ≤ ‖A‖ * ‖v‖ * ‖u (x + v) - u x‖ := hinner _ _
      _ ≤ ‖A‖ * ‖v‖ * (‖A‖ / (μ * σ) * ‖v‖) :=
        mul_le_mul_of_nonneg_left (by simpa only [add_sub_cancel_left] using hu_le (x + v) x)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  refine ⟨hconv, fun x => (hgrad x).differentiableAt, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [(hgrad x).gradient, (hgrad y).gradient, dist_eq_norm, dist_eq_norm, ← map_sub]
  calc
    ‖A.adjoint (u x - u y)‖ ≤ ‖A‖ * ‖u x - u y‖ := by
      simpa only [LinearIsometryEquiv.norm_map] using A.adjoint.le_opNorm (u x - u y)
    _ ≤ ‖A‖ * (‖A‖ / (μ * σ) * ‖x - y‖) :=
      mul_le_mul_of_nonneg_left (hu_le x y) (norm_nonneg _)
    _ = (‖A‖ ^ 2 / (μ * σ)) * ‖x - y‖ := by ring

end MathlibExt.Analysis.Convex.NesterovSmoothing
