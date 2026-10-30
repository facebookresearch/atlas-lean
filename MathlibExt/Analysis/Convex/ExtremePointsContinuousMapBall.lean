/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Segment
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Extreme points of the closed unit ball of `C(X, ℝ)`

For a compact Hausdorff space `X`, the extreme points of the closed unit
ball of the Banach space `C(X, ℝ)` of real-valued continuous functions are
exactly the functions taking only the values `±1`:

`f ∈ extremePoints ℝ (closedBall 0 1) ↔ ∀ x, |f x| = 1`.

This is the infinite-dimensional analogue of the endpoint case for finite
`ℓ^∞` spaces (see `extremePoints_closedBall_piLp_top` in
`MathlibExt/Analysis/Convex/ExtremePointsLpBalls.lean`, where the extreme
points are the vectors all of whose coordinates have norm `1`). The new
content here is the bump-function construction: if `|f x₀| < 1`, Urysohn's
lemma supplies a continuous bump supported near `x₀`, and
`f ± δ • bump` exhibits `f` as the midpoint of two distinct points of
the ball. The converse is a pointwise endpoint argument.

This is a companion to the Hahn-Banach / separation material of
`v1/Atlas/IntroductionToFunctionalAnalysis` and to the Krein-Milman
material (the extreme points here are the building blocks of the ball,
but no Krein-Milman argument is used). It is not one of the 72 v1
targets.
-/

@[expose] public section

open Set Metric ContinuousMap

namespace MathlibExt.Analysis.Convex.ExtremePointsContinuousMapBall

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The extreme points of the closed unit ball of `C(X, ℝ)`, for `X`
compact Hausdorff, are exactly the functions with `|f x| = 1` for every
`x`. -/
theorem extremePoints_closedBall_continuousMap :
    (Metric.closedBall (0 : C(X, ℝ)) 1).extremePoints ℝ = {f | ∀ x, |f x| = 1} := by
  ext f
  simp only [Set.mem_ofPred_eq]
  constructor
  · -- Forward direction: an extreme point takes only the values `±1`.
    intro hf
    rw [mem_extremePoints] at hf
    obtain ⟨hfball, hfext⟩ := hf
    have hfnorm : ‖f‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hfball
    by_contra hnot
    push Not at hnot
    obtain ⟨x₀, hx₀⟩ := hnot
    have hle : |f x₀| ≤ 1 := by
      have h := f.norm_coe_le_norm x₀
      rw [Real.norm_eq_abs] at h
      exact h.trans hfnorm
    have hlt : |f x₀| < 1 := lt_of_le_of_ne hle hx₀
    -- The radius of the bump: `δ = (1 - |f x₀|) / 2`.
    set η : ℝ := 1 - |f x₀| with hηdef
    have hη : 0 < η := sub_pos.mpr hlt
    set δ : ℝ := η / 2 with hδdef
    have hδ : 0 < δ := by positivity
    -- The neighbourhood on which `|f| < 1 - δ`.
    set U : Set X := {x | |f x| < 1 - δ} with hUdef
    have hUopen : IsOpen U := isOpen_lt f.continuous.abs continuous_const
    have hx₀U : x₀ ∈ U := by
      show |f x₀| < 1 - δ
      rw [hδdef, hηdef]
      linarith
    -- Urysohn bump: `0` outside `U`, `1` at `x₀`, values in `[0, 1]`.
    obtain ⟨φ, hφ0, hφ1, hφIcc⟩ :=
      exists_continuous_zero_one_of_isClosed hUopen.isClosed_compl isClosed_singleton
        (Set.disjoint_singleton_right.mpr (Set.notMem_compl_iff.mpr hx₀U))
    have hφx₀ : φ x₀ = 1 := by simpa using hφ1 (Set.mem_singleton x₀)
    have hφ0' : ∀ x ∈ Uᶜ, φ x = 0 := fun x hx => by simpa using hφ0 hx
    have hφmem : ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1 := fun x => hφIcc x
    have hφabs : ∀ x, |φ x| ≤ 1 := fun x =>
      abs_le.mpr ⟨by linarith [(hφmem x).1], (hφmem x).2⟩
    -- Both `f ± δ • φ` lie in the closed unit ball.
    have hball : ∀ s : C(X, ℝ), (∀ x, ‖s x‖ ≤ 1) → s ∈ Metric.closedBall (0 : C(X, ℝ)) 1 := by
      intro s hs
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (ContinuousMap.norm_le _ zero_le_one).mpr hs
    have hminus : f - δ • φ ∈ Metric.closedBall (0 : C(X, ℝ)) 1 := by
      apply hball
      intro x
      by_cases hxU : x ∈ U
      · have hfx : |f x| < 1 - δ := hxU
        have h1 : ‖(f - δ • φ) x‖ = |f x - δ * φ x| := by
          simp [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
            Real.norm_eq_abs]
        rw [h1]
        calc |f x - δ * φ x| ≤ |f x| + |δ * φ x| := abs_sub _ _
          _ ≤ |f x| + δ := by
            have h2 : |δ * φ x| = δ * |φ x| := by rw [abs_mul, abs_of_pos hδ]
            rw [h2]
            have h3 : |φ x| ≤ 1 := hφabs x
            have h4 : δ * |φ x| ≤ δ * 1 := mul_le_mul_of_nonneg_left h3 hδ.le
            linarith
          _ ≤ 1 := by linarith
      · have hφx : φ x = 0 := hφ0' x hxU
        have h1 : ‖(f - δ • φ) x‖ = |f x| := by
          simp [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul, hφx,
            Real.norm_eq_abs]
        rw [h1]
        have h := f.norm_coe_le_norm x
        rw [Real.norm_eq_abs] at h
        exact h.trans hfnorm
    have hplus : f + δ • φ ∈ Metric.closedBall (0 : C(X, ℝ)) 1 := by
      apply hball
      intro x
      by_cases hxU : x ∈ U
      · have hfx : |f x| < 1 - δ := hxU
        have h1 : ‖(f + δ • φ) x‖ = |f x + δ * φ x| := by
          simp [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul,
            Real.norm_eq_abs]
        rw [h1]
        calc |f x + δ * φ x| ≤ |f x| + |δ * φ x| := abs_add_le _ _
          _ ≤ |f x| + δ := by
            have h2 : |δ * φ x| = δ * |φ x| := by rw [abs_mul, abs_of_pos hδ]
            rw [h2]
            have h3 : |φ x| ≤ 1 := hφabs x
            have h4 : δ * |φ x| ≤ δ * 1 := mul_le_mul_of_nonneg_left h3 hδ.le
            linarith
          _ ≤ 1 := by linarith
      · have hφx : φ x = 0 := hφ0' x hxU
        have h1 : ‖(f + δ • φ) x‖ = |f x| := by
          simp [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul, hφx,
            Real.norm_eq_abs]
        rw [h1]
        have h := f.norm_coe_le_norm x
        rw [Real.norm_eq_abs] at h
        exact h.trans hfnorm
    -- But `f` is the midpoint of the two, so extremality forces `φ = 0`.
    have hseg : f ∈ openSegment ℝ (f - δ • φ) (f + δ • φ) :=
      mem_openSegment_sub_add f (δ • φ)
    obtain ⟨h1, -⟩ := hfext _ hminus _ hplus hseg
    have hzero : δ • φ = 0 := sub_eq_self.mp h1
    have hcontra : (δ • φ) x₀ = 0 := by
      have h := congrArg (fun g : C(X, ℝ) => g x₀) hzero
      simpa using h
    rw [ContinuousMap.smul_apply, hφx₀, smul_eq_mul, mul_one] at hcontra
    exact hδ.ne' hcontra
  · -- Backward direction: a `±1`-valued function is an extreme point.
    intro hf
    rw [mem_extremePoints]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      exact (ContinuousMap.norm_le _ zero_le_one).mpr fun x => by
        rw [Real.norm_eq_abs, hf x]
    · intro g₁ hg₁ g₂ hg₂ hseg
      have hgnorm1 : ‖g₁‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hg₁
      have hgnorm2 : ‖g₂‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hg₂
      obtain ⟨a, b, ha, hb, hab, hcombo⟩ := hseg
      have hpt : ∀ x, a * g₁ x + b * g₂ x = f x := by
        intro x
        have h := congrArg (fun g : C(X, ℝ) => g x) hcombo
        simpa using h
      have hpoint : ∀ x, g₁ x = f x ∧ g₂ x = f x := by
        intro x
        have hg₁x : |g₁ x| ≤ 1 := by
          have h := g₁.norm_coe_le_norm x
          rw [Real.norm_eq_abs] at h
          exact h.trans hgnorm1
        have hg₂x : |g₂ x| ≤ 1 := by
          have h := g₂.norm_coe_le_norm x
          rw [Real.norm_eq_abs] at h
          exact h.trans hgnorm2
        have hx := hpt x
        rcases eq_or_eq_neg_of_abs_eq (hf x) with hfx | hfx
        · -- `f x = 1`: both endpoints are forced to `1`.
          have hsum : a * (1 - g₁ x) + b * (1 - g₂ x) = 0 := by
            linear_combination hab - hx - hfx
          have hnn1 : 0 ≤ a * (1 - g₁ x) :=
            mul_nonneg ha.le (by linarith [abs_le.mp hg₁x])
          have hnn2 : 0 ≤ b * (1 - g₂ x) :=
            mul_nonneg hb.le (by linarith [abs_le.mp hg₂x])
          have hzero := (add_eq_zero_iff_of_nonneg hnn1 hnn2).mp hsum
          have hg : g₁ x = 1 := by
            have h := (mul_eq_zero.mp hzero.1).resolve_left ha.ne'
            linarith
          have hg' : g₂ x = 1 := by
            have h := (mul_eq_zero.mp hzero.2).resolve_left hb.ne'
            linarith
          rw [hfx]
          exact ⟨hg, hg'⟩
        · -- `f x = -1`: both endpoints are forced to `-1`.
          have hsum : a * (g₁ x + 1) + b * (g₂ x + 1) = 0 := by
            linear_combination hab + hx + hfx
          have hnn1 : 0 ≤ a * (g₁ x + 1) :=
            mul_nonneg ha.le (by linarith [abs_le.mp hg₁x])
          have hnn2 : 0 ≤ b * (g₂ x + 1) :=
            mul_nonneg hb.le (by linarith [abs_le.mp hg₂x])
          have hzero := (add_eq_zero_iff_of_nonneg hnn1 hnn2).mp hsum
          have hg : g₁ x = -1 := by
            have h := (mul_eq_zero.mp hzero.1).resolve_left ha.ne'
            linarith
          have hg' : g₂ x = -1 := by
            have h := (mul_eq_zero.mp hzero.2).resolve_left hb.ne'
            linarith
          rw [hfx]
          exact ⟨hg, hg'⟩
      constructor
      · ext x
        exact (hpoint x).1
      · ext x
        exact (hpoint x).2

/-- Membership form of `extremePoints_closedBall_continuousMap`. -/
theorem mem_extremePoints_closedBall_continuousMap {f : C(X, ℝ)} :
    f ∈ (Metric.closedBall (0 : C(X, ℝ)) 1).extremePoints ℝ ↔ ∀ x, |f x| = 1 := by
  rw [extremePoints_closedBall_continuousMap]
  simp only [Set.mem_ofPred_eq]

end MathlibExt.Analysis.Convex.ExtremePointsContinuousMapBall
