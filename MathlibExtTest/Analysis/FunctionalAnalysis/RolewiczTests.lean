/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.Rolewicz
public import MathlibExt.Analysis.InnerProductSpace.ShiftFredholmIndex
public import MathlibExt.Analysis.InnerProductSpace.SeparableHilbertBasis

import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for Rolewicz's theorem

* `2 • B`, `-2 • B` are hypercyclic on `ℓ²(ℕ, ℂ)`; `(1 / 2) • B`, `1 • B`,
  and `I • B` are not.
* `3 • B` is hypercyclic on `ℓ²(ℕ, ℝ)`; `1 • B` is not.
* Pointwise actions of powers of the shifts, the `Bⁿ Fⁿ = 1` identity,
  and the norm of a power of the forward shift.
* `#print axioms` for the `2 • B` instance: standard triple only.
-/

open Set Filter Topology Metric
open scoped _root_.lp ENNReal
open MathlibExt.Analysis.FunctionalAnalysis.Hypercyclicity
open MathlibExt.Analysis.FunctionalAnalysis.Rolewicz
open MathlibExt.Analysis.InnerProductSpace

namespace MathlibExtTest.Analysis.FunctionalAnalysis.RolewiczTests.ApproximationFixtures

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### A countable dense set in `ℓ²(ℕ, 𝕜)` -/

/-- The rational approximants in `𝕜`: `a + b * I` with `a b : ℚ`. -/
private def ratApproxScalar (q : ℚ × ℚ) : 𝕜 := (q.1 : ℝ) + (q.2 : ℝ) * RCLike.I

/-- `|im I| ≤ 1`: indeed `im I` is `0` or `1`, since
`im I * im I = im I`. -/
private theorem abs_im_I_le_one : |RCLike.im (RCLike.I : 𝕜)| ≤ 1 := by
  have h : RCLike.im (RCLike.I : 𝕜) * RCLike.im (RCLike.I : 𝕜) = RCLike.im (RCLike.I : 𝕜) :=
    RCLike.I_im (RCLike.I : 𝕜)
  have h2 : RCLike.im (RCLike.I : 𝕜) * (RCLike.im (RCLike.I : 𝕜) - 1) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp h2 with h0 | h1
  · simp [h0]
  · have hI : RCLike.im (RCLike.I : 𝕜) = 1 := sub_eq_zero.mp h1
    simp [hI]

/-- `ℚ + ℚ * I` is dense in `𝕜`. -/
private theorem dense_range_ratApproxScalar : Dense (Set.range (ratApproxScalar (𝕜 := 𝕜))) := by
  rw [dense_iff_inter_open]
  intro U hUopen hUne
  obtain ⟨z, hzU⟩ := hUne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen z hzU
  have hQ : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
  obtain ⟨q1', hq1ball, ⟨q1, hq1eq⟩⟩ :=
    hQ.inter_open_nonempty _ Metric.isOpen_ball
      ⟨RCLike.re z, Metric.mem_ball_self (half_pos hε)⟩
  obtain ⟨q2', hq2ball, ⟨q2, hq2eq⟩⟩ :=
    hQ.inter_open_nonempty _ Metric.isOpen_ball
      ⟨RCLike.im z, Metric.mem_ball_self (half_pos hε)⟩
  have hq1 : |(q1 : ℝ) - RCLike.re z| < ε / 2 := by
    have h := Metric.mem_ball.mp hq1ball
    rw [← hq1eq, Real.dist_eq] at h
    exact h
  have hq2 : |(q2 : ℝ) - RCLike.im z| < ε / 2 := by
    have h := Metric.mem_ball.mp hq2ball
    rw [← hq2eq, Real.dist_eq] at h
    exact h
  refine ⟨ratApproxScalar (q1, q2), ?_, ⟨⟨q1, q2⟩, rfl⟩⟩
  apply hball
  rw [Metric.mem_ball]
  -- The difference `ratApproxScalar (q1, q2) - z` has small real and imaginary parts.
  set w := ratApproxScalar (q1, q2) - z with hw
  have hreS : RCLike.re ((ratApproxScalar (𝕜 := 𝕜)) (q1, q2)) = (q1 : ℝ) := by
    simp [ratApproxScalar]
  have himS : RCLike.im ((ratApproxScalar (𝕜 := 𝕜)) (q1, q2)) =
      (q2 : ℝ) * RCLike.im (RCLike.I : 𝕜) := by
    simp [ratApproxScalar]
  have hrew : RCLike.re w = (q1 : ℝ) - RCLike.re z := by
    rw [hw, map_sub, hreS]
  have himw : RCLike.im w = ((q2 : ℝ) - RCLike.im z) * RCLike.im (RCLike.I : 𝕜) := by
    have h2 : RCLike.im w = RCLike.im (ratApproxScalar (q1, q2)) - RCLike.im z :=
      map_sub _ _ _
    rw [h2, himS]
    linear_combination RCLike.I_im z
  have hre : |RCLike.re w| < ε / 2 := by rw [hrew]; exact hq1
  have him : |RCLike.im w| < ε / 2 := by
    rw [himw, abs_mul]
    calc |(q2 : ℝ) - RCLike.im z| * |RCLike.im (RCLike.I : 𝕜)|
        ≤ |(q2 : ℝ) - RCLike.im z| * 1 :=
          mul_le_mul_of_nonneg_left abs_im_I_le_one (abs_nonneg _)
      _ = |(q2 : ℝ) - RCLike.im z| := mul_one _
      _ < ε / 2 := hq2
  have hre2 : RCLike.re w * RCLike.re w < (ε / 2) * (ε / 2) := by
    have h := abs_lt.mp hre
    nlinarith [mul_pos (sub_pos.mpr h.2)
      (show (0 : ℝ) < ε / 2 + RCLike.re w from by linarith [h.1, hε])]
  have him2 : RCLike.im w * RCLike.im w < (ε / 2) * (ε / 2) := by
    have h := abs_lt.mp him
    nlinarith [mul_pos (sub_pos.mpr h.2)
      (show (0 : ℝ) < ε / 2 + RCLike.im w from by linarith [h.1, hε])]
  have hsq : ‖w‖ ^ 2 < ε ^ 2 := by
    rw [RCLike.norm_sq_eq_def]
    nlinarith [hre2, him2, mul_pos hε hε]
  have hnorm : ‖w‖ < ε := by
    have h := abs_lt_of_sq_lt_sq hsq (le_of_lt hε)
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  rw [dist_eq_norm]
  exact hnorm

/-- Finite sequences with coefficients in `ℚ + ℚ * I`: the index is a
finite set `s` together with a rational pair for each `i ∈ s`. The
index type is countable, since `s` is finite. -/
private noncomputable def ratApproxSeq (p : Σ s : Finset ℕ, (s → ℚ × ℚ)) : ℓ²(ℕ, 𝕜) :=
  ∑ i : ↥p.1, lp.single 2 (i : ℕ) ((ratApproxScalar (𝕜 := 𝕜)) (p.2 i))

/-- The finite `ℚ + ℚ * I`-coefficient sequences are dense in `ℓ²(ℕ, 𝕜)`. -/
private theorem dense_range_ratApproxSeq : Dense (Set.range (ratApproxSeq (𝕜 := 𝕜))) := by
  rw [dense_iff_inter_open]
  intro U hUopen hUne
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUopen x hxU
  have hT := (lp.hasSum_single (by simp : (2 : ℝ≥0∞) ≠ ⊤) x).tendsto_sum_nat
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hT) (ε / 2) (half_pos hε)
  -- The truncation of `x` to the first `N` coordinates is within `ε / 2` of `x`.
  set s₀ := Finset.range N with hs₀
  have htrunc : dist (∑ i ∈ s₀, lp.single 2 i ((x : ℕ → 𝕜) i)) x < ε / 2 := hN N le_rfl
  -- Approximate each coefficient of the truncation by a rational approximant.
  set c : ℝ := (s₀.card : ℝ) with hc
  set δ : ℝ := ε / (2 * (c + 1)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    exact div_pos hε (mul_pos two_pos (by linarith))
  have hchoice : ∀ i ∈ s₀, ∃ q : ℚ × ℚ, ‖(x : ℕ → 𝕜) i - ratApproxScalar q‖ < δ := by
    intro i _
    obtain ⟨y, hyball, ⟨q, hq⟩⟩ :=
      dense_range_ratApproxScalar.inter_open_nonempty _ Metric.isOpen_ball
        ⟨(x : ℕ → 𝕜) i, Metric.mem_ball_self hδpos⟩
    refine ⟨q, ?_⟩
    have hd : dist y ((x : ℕ → 𝕜) i) < δ := Metric.mem_ball.mp hyball
    rw [← hq, dist_eq_norm, norm_sub_rev] at hd
    exact hd
  have hchoice' : ∀ i, ∃ q : ℚ × ℚ, i ∈ s₀ → ‖(x : ℕ → 𝕜) i - ratApproxScalar q‖ < δ := by
    intro i
    by_cases hi : i ∈ s₀
    · obtain ⟨q, hq⟩ := hchoice i hi
      exact ⟨q, fun _ => hq⟩
    · exact ⟨(0, 0), fun h => absurd h hi⟩
  choose g hg using hchoice'
  -- The rational approximant `y` is within `ε / 2` of the truncation.
  set g' : ↥s₀ → ℚ × ℚ := fun i => g (i : ℕ) with hg'
  set y : ℓ²(ℕ, 𝕜) := ratApproxSeq ⟨s₀, g'⟩ with hy
  have hy_rat : y = ∑ i ∈ s₀, lp.single 2 i (ratApproxScalar (g i)) := by
    change (∑ i : ↥s₀, lp.single 2 (i : ℕ) (ratApproxScalar (g' i))) = _
    exact Finset.sum_attach s₀ (fun i => lp.single 2 i (ratApproxScalar (g i)))
  have hdiff : y - ∑ i ∈ s₀, lp.single 2 i ((x : ℕ → 𝕜) i) =
      ∑ i ∈ s₀, lp.single 2 i (ratApproxScalar (g i) - (x : ℕ → 𝕜) i) := by
    rw [hy_rat, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => (lp.single_sub 2 i _ _).symm
  have hnorm2 : ‖y - ∑ i ∈ s₀, lp.single 2 i ((x : ℕ → 𝕜) i)‖ ^ 2 < (ε / 2) ^ 2 := by
    have hsum : ‖∑ i ∈ s₀, lp.single 2 i (ratApproxScalar (g i) - (x : ℕ → 𝕜) i)‖ ^ (2 : ℝ) =
        ∑ i ∈ s₀, ‖ratApproxScalar (g i) - (x : ℕ → 𝕜) i‖ ^ (2 : ℝ) := by
      have h := lp.norm_sum_single (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
        (fun i => ratApproxScalar (g i) - (x : ℕ → 𝕜) i) s₀
      rwa [show (2 : ℝ≥0∞).toReal = (2 : ℝ) from by simp] at h
    have hsum2 : ‖∑ i ∈ s₀, lp.single 2 i (ratApproxScalar (g i) - (x : ℕ → 𝕜) i)‖ ^ 2 =
        ∑ i ∈ s₀, ‖ratApproxScalar (g i) - (x : ℕ → 𝕜) i‖ ^ 2 := by
      have h := hsum
      simp only [Real.rpow_two] at h
      exact h
    rw [hdiff, hsum2]
    have hterm : ∀ i ∈ s₀, ‖ratApproxScalar (g i) - (x : ℕ → 𝕜) i‖ ^ 2 < δ ^ 2 := by
      intro i hi
      have h := hg i hi
      rw [norm_sub_rev] at h
      nlinarith [mul_pos (sub_pos.mpr h)
        (show (0 : ℝ) < δ + ‖ratApproxScalar (g i) - (x : ℕ → 𝕜) i‖ from by
          linarith [norm_nonneg (ratApproxScalar (g i) - (x : ℕ → 𝕜) i), hδpos])]
    have hsumle : ∑ i ∈ s₀, ‖ratApproxScalar (g i) - (x : ℕ → 𝕜) i‖ ^ 2 ≤ s₀.card • δ ^ 2 :=
      Finset.sum_le_card_nsmul s₀ _ _ fun i hi => le_of_lt (hterm i hi)
    have hcard : (s₀.card : ℝ) * δ ^ 2 < (ε / 2) ^ 2 := by
      have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
      have hc1 : (0 : ℝ) < c + 1 := by linarith
      have hlt : c < (c + 1) ^ 2 := by nlinarith [sq_nonneg c]
      have hfrac : c / (c + 1) ^ 2 < 1 := by
        rw [div_lt_one (pow_pos hc1 2)]
        exact hlt
      have heq : (s₀.card : ℝ) * δ ^ 2 = (c / (c + 1) ^ 2) * (ε / 2) ^ 2 := by
        rw [hδ, ← hc]
        field_simp
      rw [heq]
      calc (c / (c + 1) ^ 2) * (ε / 2) ^ 2
          < 1 * (ε / 2) ^ 2 :=
            mul_lt_mul_of_pos_right hfrac (pow_pos (half_pos hε) 2)
        _ = (ε / 2) ^ 2 := one_mul _
    rw [nsmul_eq_mul] at hsumle
    have hc_eq : (s₀.card : ℝ) = c := rfl
    rw [hc_eq] at hsumle
    exact lt_of_le_of_lt hsumle hcard
  have hnorm : ‖y - ∑ i ∈ s₀, lp.single 2 i ((x : ℕ → 𝕜) i)‖ < ε / 2 := by
    have h := abs_lt_of_sq_lt_sq hnorm2 (le_of_lt (half_pos hε))
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  refine ⟨y, ?_, ⟨⟨s₀, g'⟩, rfl⟩⟩
  apply hball
  rw [Metric.mem_ball]
  have hdist : dist y x ≤ dist y (∑ i ∈ s₀, lp.single 2 i ((x : ℕ → 𝕜) i)) +
      dist (∑ i ∈ s₀, lp.single 2 i ((x : ℕ → 𝕜) i)) x := dist_triangle _ _ _
  rw [dist_eq_norm] at htrunc
  simp only [dist_eq_norm] at hdist
  rw [dist_eq_norm]
  linarith [hnorm, htrunc]


end MathlibExtTest.Analysis.FunctionalAnalysis.RolewiczTests.ApproximationFixtures

open MathlibExtTest.Analysis.FunctionalAnalysis.RolewiczTests.ApproximationFixtures

namespace MathlibExtTest.Analysis.FunctionalAnalysis.RolewiczTests

/-- `2 • B` is hypercyclic on `ℓ²(ℕ, ℂ)`. -/
theorem rolewicz_two_complex : IsHypercyclic ((2 : ℂ) • LpShiftOperator.backwardCLM (𝕜 := ℂ)) :=
  (isHypercyclic_smul_backwardShiftCLM_iff (2 : ℂ)).mpr (by
    rw [Complex.norm_two]
    norm_num)

/-- `-2 • B` is hypercyclic on `ℓ²(ℕ, ℂ)`. -/
example : IsHypercyclic (((-2 : ℂ)) • LpShiftOperator.backwardCLM (𝕜 := ℂ)) := by
  rw [isHypercyclic_smul_backwardShiftCLM_iff, norm_neg, Complex.norm_two]
  norm_num

/-- `(1 / 2) • B` is not hypercyclic on `ℓ²(ℕ, ℂ)`. -/
example : ¬ IsHypercyclic (((1 / 2 : ℂ)) • LpShiftOperator.backwardCLM (𝕜 := ℂ)) := by
  rw [isHypercyclic_smul_backwardShiftCLM_iff, Complex.norm_div, norm_one,
    Complex.norm_two]
  norm_num

/-- `1 • B` is not hypercyclic on `ℓ²(ℕ, ℂ)`. -/
example : ¬ IsHypercyclic (((1 : ℂ)) • LpShiftOperator.backwardCLM (𝕜 := ℂ)) := by
  rw [isHypercyclic_smul_backwardShiftCLM_iff, norm_one]
  norm_num

/-- `I • B` is not hypercyclic on `ℓ²(ℕ, ℂ)`: `‖I‖ = 1`. -/
example : ¬ IsHypercyclic (Complex.I • LpShiftOperator.backwardCLM (𝕜 := ℂ)) := by
  rw [isHypercyclic_smul_backwardShiftCLM_iff, Complex.norm_I]
  norm_num

/-- `3 • B` is hypercyclic on `ℓ²(ℕ, ℝ)`. -/
example : IsHypercyclic ((3 : ℝ) • LpShiftOperator.backwardCLM (𝕜 := ℝ)) := by
  rw [isHypercyclic_smul_backwardShiftCLM_iff (𝕜 := ℝ)]
  norm_num

/-- `1 • B` is not hypercyclic on `ℓ²(ℕ, ℝ)`. -/
example : ¬ IsHypercyclic (((1 : ℝ)) • LpShiftOperator.backwardCLM (𝕜 := ℝ)) := by
  rw [isHypercyclic_smul_backwardShiftCLM_iff (𝕜 := ℝ), norm_one]
  norm_num

/-- The second power of the backward shift drops two coordinates. -/
example (x : ℓ²(ℕ, ℂ)) : (LpShiftOperator.backwardCLM (𝕜 := ℂ) ^ 2) x 3 = x 5 :=
  ShiftFredholmIndex.backwardCLM_pow_apply 2 x 3

/-- The second power of the forward shift vanishes in coordinate `0`. -/
example (x : ℓ²(ℕ, ℂ)) : (LpShiftOperator.shiftCLM (𝕜 := ℂ) ^ 2) x 0 = 0 := by
  rw [ShiftFredholmIndex.shiftCLM_pow_apply]
  simp

/-- `B F = 1` on the first basis vector. -/
example : (LpShiftOperator.backwardCLM (𝕜 := ℂ) ^ 1)
    ((LpShiftOperator.shiftCLM (𝕜 := ℂ) ^ 1) (lp.single 2 0 (1 : ℂ))) =
    lp.single 2 0 (1 : ℂ) := by
  simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using
      DFunLike.congr_fun
        (ShiftFredholmIndex.backwardCLM_pow_comp_shiftCLM_pow (𝕜 := ℂ) 1)
        (lp.single 2 0 (1 : ℂ))

/-- Powers of the forward shift preserve norms. -/
example (x : ℓ²(ℕ, ℂ)) : ‖(LpShiftOperator.shiftCLM (𝕜 := ℂ) ^ 3) x‖ = ‖x‖ :=
  norm_forwardShiftCLM_pow_apply 3 x

/-- `ℚ + ℚ * I` is dense in `ℂ`; the approximant for `(1 / 2, 1 / 3)`
lies in its range. -/
example : ratApproxScalar (𝕜 := ℂ) (1 / 2, 1 / 3) ∈
    Set.range (ratApproxScalar (𝕜 := ℂ)) :=
  ⟨(1 / 2, 1 / 3), rfl⟩

#print axioms rolewicz_two_complex

/-- A nonreal scalar of norm two makes the canonical backward shift hypercyclic. -/
example : IsHypercyclic ((2 * Complex.I : ℂ) • LpShiftOperator.backwardCLM (𝕜 := ℂ)) := by
  rw [isHypercyclic_smul_backwardShiftCLM_iff, norm_mul,
    Complex.norm_two, Complex.norm_I, mul_one]
  norm_num

/-- Reversing the shift composition loses the first basis vector. -/
example : (LpShiftOperator.shiftCLM (𝕜 := ℂ) ∘L LpShiftOperator.backwardCLM)
    (lp.single 2 0 (1 : ℂ)) = 0 := by
  ext i
  cases i <;> simp [ContinuousLinearMap.comp_apply, LpShiftOperator.shiftCLM_apply,
    LpShiftOperator.backwardCLM_apply, lp.single_apply]

/-- Scalar powers and canonical backward powers have the correct coordinate action. -/
example (μ : ℂ) (n : ℕ) (x : ℓ²(ℕ, ℂ)) :
    (((μ • LpShiftOperator.backwardCLM (𝕜 := ℂ)) ^ n) x) 0 = μ ^ n * x n := by
  rw [smul_backwardShiftCLM_pow_apply, lp.coeFn_smul, Pi.smul_apply,
    ShiftFredholmIndex.backwardCLM_pow_apply, Nat.zero_add, smul_eq_mul]

end MathlibExtTest.Analysis.FunctionalAnalysis.RolewiczTests

/-! The countable-density API and the concrete approximation contracts used below. -/

example {𝕜 : Type*} [RCLike 𝕜] : TopologicalSpace.SeparableSpace (ℓ²(ℕ, 𝕜)) :=
  SeparableHilbertBasis.separableSpace_of_countable_hilbertBasis
    (default : HilbertBasis ℕ 𝕜 ℓ²(ℕ, 𝕜))

example {𝕜 : Type*} [RCLike 𝕜] :
    Dense (Set.range (ratApproxScalar (𝕜 := 𝕜))) :=
  dense_range_ratApproxScalar

example {𝕜 : Type*} [RCLike 𝕜] :
    Dense (Set.range (ratApproxSeq (𝕜 := 𝕜))) :=
  dense_range_ratApproxSeq
