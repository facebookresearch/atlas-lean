/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Analysis.Convex.Deriv

/-!
# Classification-calibrated surrogate losses

Bartlett, Jordan and McAuliffe (*Convexity, classification, and risk bounds*, J. Amer. Statist.
Assoc. 101, 2006; technical report version at
<https://www.stat.berkeley.edu/~bartlett/papers/bjm-ccrb-05.pdf>, whose numbering of
definitions, theorems and lemmas is used throughout; Section 2.2) study a
nonnegative margin loss `φ : ℝ → [0, ∞)` used in place of the 0-1 loss. For a conditional
probability `η = P(Y = 1 | X = x) ∈ [0, 1]` and a real prediction `α`, the conditional
`φ`-risk is

`C_η(α) = η φ(α) + (1 - η) φ(-α)`   (`condRisk`),

its optimal value is `H(η) = inf_α C_η(α)` (`optRisk`), and its optimal value under the
constraint that `α` has the wrong sign, `α (2η - 1) ≤ 0`, is `H⁻(η)` (`wrongSignRisk`). The
loss is **classification-calibrated** (their Definition 1) if `H⁻(η) > H(η)` for every
`η ≠ 1/2`: forcing the wrong sign always costs a strictly positive amount of `φ`-risk.

Main results:

* `isClassificationCalibrated_iff_differentiableAt_and_deriv_neg`: a nonnegative convex `φ` is
  classification-calibrated if and only if it is differentiable at `0` with `φ'(0) < 0` (their
  Theorem 4, part 1).
* `isClassificationCalibrated_of_hasDerivAt`: the sufficiency half. Hinge, exponential and
  logistic losses are examples.
* `differentiableAt_and_deriv_neg_of_isClassificationCalibrated`: the necessity half, which
  holds for every convex `φ : ℝ → ℝ`. If the right derivative of `C_η` at `0`,
  `η φ'₊(0) - (1 - η) φ'₋(0)`, is nonnegative for some `η ∈ (1/2, 1]`, then `H⁻(η) ≤ H(η)`;
  `η = 1` excludes `φ'₊(0) ≥ 0`, and `η = φ'₋(0) / (φ'₋(0) + φ'₊(0))` excludes
  `φ'₋(0) < φ'₊(0) < 0`.
* `optRisk_one_sub`, `wrongSignRisk_one_sub`: `H` and `H⁻` are symmetric about `1/2` (their
  Lemma 6, part 1).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.ClassificationCalibration

open Filter Topology

/-- The **conditional `φ`-risk** `C_η(α) = η φ(α) + (1 - η) φ(-α)` of the prediction `α` when
`P(Y = 1 | X = x) = η` (Bartlett, Jordan and McAuliffe, *Convexity, classification, and risk
bounds*, Section 2.2). -/
def condRisk (φ : ℝ → ℝ) (η α : ℝ) : ℝ := η * φ α + (1 - η) * φ (-α)

/-- The **optimal conditional `φ`-risk** `H(η) = inf_α C_η(α)` (Bartlett, Jordan and McAuliffe,
Section 2.2), an infimum in `ℝ`. -/
noncomputable def optRisk (φ : ℝ → ℝ) (η : ℝ) : ℝ := ⨅ α : ℝ, condRisk φ η α

/-- The **optimal conditional `φ`-risk with the wrong sign**
`H⁻(η) = inf_{α (2η - 1) ≤ 0} C_η(α)` (Bartlett, Jordan and McAuliffe, Section 2.2). -/
noncomputable def wrongSignRisk (φ : ℝ → ℝ) (η : ℝ) : ℝ :=
  ⨅ α : {α : ℝ // α * (2 * η - 1) ≤ 0}, condRisk φ η α

/-- A loss `φ` is **classification-calibrated** if `H(η) < H⁻(η)` for every `η ∈ [0, 1]` with
`η ≠ 1/2` (Bartlett, Jordan and McAuliffe, Definition 1). The definition is meant for
nonnegative (or at least bounded-below) `φ`, as in the source, which takes `φ : ℝ → [0, ∞)`;
otherwise the infima `H` and `H⁻`, taken in `ℝ`, can be junk values. -/
def IsClassificationCalibrated (φ : ℝ → ℝ) : Prop :=
  ∀ η ∈ Set.Icc (0 : ℝ) 1, η ≠ 1 / 2 → optRisk φ η < wrongSignRisk φ η

variable {φ : ℝ → ℝ}

lemma condRisk_nonneg (h0 : ∀ x, 0 ≤ φ x) {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) 1) (α : ℝ) :
    0 ≤ condRisk φ η α := by
  unfold condRisk
  have := hη.1; have := hη.2
  have := h0 α; have := h0 (-α)
  positivity

/-- Exchanging `η` and `1 - η` reflects the conditional risk: `C_{1-η}(α) = C_η(-α)`. -/
lemma condRisk_one_sub (φ : ℝ → ℝ) (η α : ℝ) : condRisk φ (1 - η) α = condRisk φ η (-α) := by
  simp only [condRisk, neg_neg]; ring

/-- `H` is symmetric about `1/2`: `H(1 - η) = H(η)` (Bartlett, Jordan and McAuliffe,
Lemma 6, part 1). -/
theorem optRisk_one_sub (φ : ℝ → ℝ) (η : ℝ) : optRisk φ (1 - η) = optRisk φ η := by
  unfold optRisk
  simp only [condRisk_one_sub]
  exact (Equiv.neg ℝ).iInf_comp (g := fun α => condRisk φ η α)

/-- `H⁻` is symmetric about `1/2`: `H⁻(1 - η) = H⁻(η)` (Bartlett, Jordan and McAuliffe,
Lemma 6, part 1). -/
theorem wrongSignRisk_one_sub (φ : ℝ → ℝ) (η : ℝ) :
    wrongSignRisk φ (1 - η) = wrongSignRisk φ η := by
  unfold wrongSignRisk
  let e : {α : ℝ // α * (2 * (1 - η) - 1) ≤ 0} ≃ {α : ℝ // α * (2 * η - 1) ≤ 0} :=
    (Equiv.neg ℝ).subtypeEquiv fun α => by
      simp only [Equiv.neg_apply]
      constructor <;> intro h <;> nlinarith
  rw [← e.iInf_comp]
  congr 1
  funext α
  simp [e, condRisk_one_sub]

/-- The key case `η > 1/2`: if `φ` is nonnegative and convex, differentiable at `0` with
`φ'(0) < 0`, then forcing a nonpositive prediction strictly increases the optimal conditional
risk. -/
lemma optRisk_lt_wrongSignRisk_of_half_lt (h0 : ∀ x, 0 ≤ φ x) (hconv : ConvexOn ℝ Set.univ φ)
    {d : ℝ} (hd : HasDerivAt φ d 0) (hdneg : d < 0) {η : ℝ} (hη : 1 / 2 < η) (hη1 : η ≤ 1) :
    optRisk φ η < wrongSignRisk φ η := by
  set C : ℝ → ℝ := condRisk φ η with hC
  have hmem : η ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, hη1⟩
  have hbdd : BddBelow (Set.range C) := ⟨0, by
    rintro _ ⟨α, rfl⟩; exact condRisk_nonneg h0 hmem α⟩
  -- the derivative of `C` at `0` is `(2η - 1) d < 0`
  have hneg : HasDerivAt (fun α : ℝ => φ (-α)) (d * (-1)) 0 := by
    have h1 : HasDerivAt φ d (-0) := by simpa using hd
    exact h1.comp 0 (hasDerivAt_neg 0)
  have hCd : HasDerivAt C (η * d + (1 - η) * (d * (-1))) 0 :=
    (HasDerivAt.const_mul η hd).add (HasDerivAt.const_mul (1 - η) hneg)
  have hslope : η * d + (1 - η) * (d * (-1)) < 0 := by nlinarith
  -- some `ε > 0` has `C ε < C 0`
  obtain ⟨ε, hεneg, hεpos⟩ : ∃ ε : ℝ, ε⁻¹ • (C (0 + ε) - C 0) < 0 ∧ 0 < ε :=
    ((hCd.tendsto_slope_zero_right.eventually (gt_mem_nhds hslope)).and
      self_mem_nhdsWithin).exists
  have hCε : C ε < C 0 := by
    rw [zero_add, smul_eq_mul] at hεneg
    have := (mul_neg_iff.1 hεneg)
    rcases this with ⟨h1, h2⟩ | ⟨h1, _⟩
    · linarith
    · exact absurd h1 (not_lt.2 (inv_pos.2 hεpos).le)
  -- convexity: `C 0 ≤ C α` for every `α ≤ 0`
  have hCconv : ∀ α : ℝ, α ≤ 0 → C 0 ≤ C α := by
    intro α hα
    rcases hα.eq_or_lt with rfl | hα
    · exact le_rfl
    set a : ℝ := ε / (ε - α) with ha
    set b : ℝ := -α / (ε - α) with hb
    have hden : 0 < ε - α := by linarith
    have ha0 : 0 ≤ a := div_nonneg hεpos.le hden.le
    have hb0 : 0 ≤ b := div_nonneg (by linarith) hden.le
    have hab : a + b = 1 := by rw [ha, hb, ← add_div]; field_simp; ring
    have hpt : a • α + b • ε = 0 := by
      simp only [smul_eq_mul, ha, hb]; field_simp; ring
    have hpt' : a • (-α) + b • (-ε) = 0 := by
      simp only [smul_eq_mul, ha, hb]; field_simp; ring
    have h1 := hconv.2 (Set.mem_univ α) (Set.mem_univ ε) ha0 hb0 hab
    have h2 := hconv.2 (Set.mem_univ (-α)) (Set.mem_univ (-ε)) ha0 hb0 hab
    rw [hpt] at h1; rw [hpt'] at h2
    simp only [smul_eq_mul] at h1 h2
    have hconvC : C 0 ≤ a * C α + b * C ε := by
      simp only [hC, condRisk, neg_zero]
      have hη0 : 0 ≤ η := hmem.1
      have hη1' : 0 ≤ 1 - η := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h1 hη0, mul_le_mul_of_nonneg_left h2 hη1']
    have hapos : 0 < a := div_pos hεpos hden
    have hbC : b * C ε ≤ b * C 0 := mul_le_mul_of_nonneg_left hCε.le hb0
    have haC : a * C 0 ≤ a * C α := by
      have e : a * C 0 = C 0 - b * C 0 := by rw [show a = 1 - b by linarith]; ring
      linarith
    exact le_of_mul_le_mul_left haC hapos
  -- conclude
  have hW : C 0 ≤ wrongSignRisk φ η := by
    have : Nonempty {α : ℝ // α * (2 * η - 1) ≤ 0} := ⟨⟨0, by simp⟩⟩
    refine le_ciInf fun α => hCconv α ?_
    have := α.2
    by_contra h
    push Not at h
    have : 0 < (α : ℝ) * (2 * η - 1) := mul_pos h (by linarith)
    linarith
  have hH : optRisk φ η ≤ C ε := ciInf_le hbdd ε
  linarith

/-- **Convex losses with negative slope at `0` are classification-calibrated** (Bartlett,
Jordan and McAuliffe, *Convexity, classification, and risk bounds*, Theorem 4, part 1, the
sufficiency direction): if `φ : ℝ → [0, ∞)` is convex and differentiable at `0` with
`φ'(0) < 0`, then `φ` is classification-calibrated. -/
theorem isClassificationCalibrated_of_hasDerivAt (h0 : ∀ x, 0 ≤ φ x)
    (hconv : ConvexOn ℝ Set.univ φ) {d : ℝ} (hd : HasDerivAt φ d 0) (hdneg : d < 0) :
    IsClassificationCalibrated φ := by
  intro η hη hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h := optRisk_lt_wrongSignRisk_of_half_lt h0 hconv hd hdneg (η := 1 - η)
      (by linarith) (by linarith [hη.1])
    rwa [optRisk_one_sub, wrongSignRisk_one_sub] at h
  · exact optRisk_lt_wrongSignRisk_of_half_lt h0 hconv hd hdneg hgt hη.2

/-- The key case of the necessity direction: for a convex `φ` and `1/2 ≤ η ≤ 1`, if the right
derivative `η φ'₊(0) - (1 - η) φ'₋(0)` of `C_η` at `0` is nonnegative, then `C_η` is at least
`C_η(0)` on `(0, ∞)`, so a prediction of the wrong sign does as well as any: `H⁻(η) ≤ H(η)`. -/
private lemma wrongSignRisk_le_optRisk_of_rightDeriv_nonneg (hconv : ConvexOn ℝ Set.univ φ)
    {η : ℝ} (hη : 1 / 2 ≤ η) (hη1 : η ≤ 1)
    (h : (1 - η) * derivWithin φ (Set.Iio 0) 0 ≤ η * derivWithin φ (Set.Ioi 0) 0) :
    wrongSignRisk φ η ≤ optRisk φ η := by
  have hint : (0 : ℝ) ∈ interior Set.univ := by simp
  have hpos : ∀ α : ℝ, 0 < α → condRisk φ η 0 ≤ condRisk φ η α := by
    intro α hα
    have h1 := hconv.rightDeriv_le_slope_of_mem_interior hint (Set.mem_univ α) hα
    have h2 := hconv.slope_le_leftDeriv_of_mem_interior (Set.mem_univ (-α)) hint (neg_lt_zero.2 hα)
    rw [slope_def_field, sub_zero, le_div_iff₀ hα] at h1
    rw [slope_def_field, zero_sub, neg_neg, div_le_iff₀ hα] at h2
    have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ η by linarith)
    have h4 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 1 - η by linarith)
    have h5 := mul_le_mul_of_nonneg_left h hα.le
    simp only [condRisk, neg_zero]
    nlinarith
  have hdom : ∀ α : ℝ, ∃ β : {α : ℝ // α * (2 * η - 1) ≤ 0}, condRisk φ η β ≤ condRisk φ η α := by
    intro α
    rcases le_or_gt α 0 with hα | hα
    · exact ⟨⟨α, mul_nonpos_of_nonpos_of_nonneg hα (by linarith)⟩, le_rfl⟩
    · exact ⟨⟨0, by simp⟩, hpos α hα⟩
  unfold optRisk wrongSignRisk
  by_cases hb : BddBelow (Set.range fun β : {α : ℝ // α * (2 * η - 1) ≤ 0} => condRisk φ η β)
  · exact le_ciInf fun α => (hdom α).elim fun β hβ => ciInf_le_of_le hb β hβ
  · have hb' : ¬BddBelow (Set.range fun α : ℝ => condRisk φ η α) := fun ⟨m, hm⟩ =>
      hb ⟨m, by rintro _ ⟨β, rfl⟩; exact hm ⟨β, rfl⟩⟩
    rw [Real.iInf_of_not_bddBelow hb, Real.iInf_of_not_bddBelow hb']

/-- **Classification-calibrated convex losses have negative slope at 0** (Bartlett, Jordan and
McAuliffe, *Convexity, classification, and risk bounds*, Theorem 4, part 1, the necessity
direction): if `φ : ℝ → ℝ` is convex and classification-calibrated, then `φ` is differentiable
at `0` and `φ'(0) < 0`. This direction does not need `φ` to be nonnegative; here `H` and `H⁻`
are infima in `ℝ`, which are `0` for a family unbounded below. -/
theorem differentiableAt_and_deriv_neg_of_isClassificationCalibrated
    (hconv : ConvexOn ℝ Set.univ φ) (hcal : IsClassificationCalibrated φ) :
    DifferentiableAt ℝ φ 0 ∧ deriv φ 0 < 0 := by
  set a := derivWithin φ (Set.Iio 0) 0
  set b := derivWithin φ (Set.Ioi 0) 0
  have hint : (0 : ℝ) ∈ interior Set.univ := by simp
  -- calibration at `η` fails as soon as `(1 - η) φ'₋(0) ≤ η φ'₊(0)`
  have key : ∀ η : ℝ, 1 / 2 < η → η ≤ 1 → ¬(1 - η) * a ≤ η * b := fun η hη hη1 h =>
    (wrongSignRisk_le_optRisk_of_rightDeriv_nonneg hconv hη.le hη1 h).not_gt
      (hcal η ⟨by linarith, hη1⟩ hη.ne')
  have hb : b < 0 := by
    by_contra hb
    exact key 1 (by norm_num) le_rfl (by linarith)
  have hab : a = b := by
    by_contra hne
    have hlt : a < b := (hconv.leftDeriv_le_rightDeriv_of_mem_interior hint).lt_of_ne hne
    have hsum : a + b < 0 := by linarith
    refine key (a / (a + b)) ?_ ?_ (le_of_eq ?_)
    · rw [lt_div_iff_of_neg hsum]; linarith
    · rw [div_le_one_of_neg hsum]; linarith
    · field_simp [hsum.ne]; ring
  have hd : HasDerivAt φ b 0 := by
    rw [hasDerivAt_iff_tendsto_slope_left_right]
    constructor
    · rw [← hasDerivWithinAt_iff_tendsto_slope' Set.self_notMem_Iio, ← hab]
      exact hconv.hasDerivWithinAt_leftDeriv_of_mem_interior hint
    · rw [← hasDerivWithinAt_iff_tendsto_slope' Set.self_notMem_Ioi]
      exact hconv.hasDerivWithinAt_rightDeriv_of_mem_interior hint
  exact ⟨hd.differentiableAt, hd.deriv ▸ hb⟩

/-- **Classification calibration of convex margin losses** (Bartlett, Jordan and McAuliffe,
*Convexity, classification, and risk bounds*, Theorem 4, part 1): a convex loss
`φ : ℝ → [0, ∞)` is classification-calibrated if and only if it is differentiable at `0` and
`φ'(0) < 0`. -/
theorem isClassificationCalibrated_iff_differentiableAt_and_deriv_neg (h0 : ∀ x, 0 ≤ φ x)
    (hconv : ConvexOn ℝ Set.univ φ) :
    IsClassificationCalibrated φ ↔ DifferentiableAt ℝ φ 0 ∧ deriv φ 0 < 0 :=
  ⟨differentiableAt_and_deriv_neg_of_isClassificationCalibrated hconv,
    fun h => isClassificationCalibrated_of_hasDerivAt h0 hconv h.1.hasDerivAt h.2⟩

end Cslib.MachineLearning.ClassificationCalibration
