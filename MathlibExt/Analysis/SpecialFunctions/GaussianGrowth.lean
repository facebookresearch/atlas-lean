/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.GaussianMoments
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Gaussian domination of exponential growth

Gaussian decay dominates every polynomial times exponential growth in `|x|`.
Damping an exponentially growing datum by any positive Gaussian makes it bounded;
locally shifting the Gaussian decay parameter therefore reuses the bounded-data
moment calculus. The original moments are jointly smooth for every positive
Gaussian decay parameter.

These are the classical completing-square estimates behind the heat construction
in Gesztesy and Holden, *The Cole–Hopf and Miura transformations revisited*,
Remark 3.5, https://arxiv.org/abs/solv-int/9812025. We treat at most exponential
rather than quadratic-exponential growth, so no finite-time restriction occurs.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Real
open scoped ContDiff

namespace MathlibExt.Analysis

/-- A real datum has at most exponential growth in the absolute spatial variable. -/
def HasExpGrowth (f : ℝ → ℝ) : Prop :=
  ∃ M c : ℝ, 0 ≤ M ∧ 0 ≤ c ∧ ∀ x, |f x| ≤ M * exp (c * |x|)

/-- Bounded data are included, with growth rate zero. -/
theorem HasExpGrowth.of_bounded {f : ℝ → ℝ} (hb : ∃ M, ∀ x, |f x| ≤ M) :
    HasExpGrowth f := by
  obtain ⟨M, hM⟩ := hb
  exact ⟨M, 0, (abs_nonneg (f 0)).trans (hM 0), le_rfl, by simpa using hM⟩

/-- Scalar multiplication preserves at most exponential growth. -/
theorem HasExpGrowth.const_mul {f : ℝ → ℝ} (hg : HasExpGrowth f) (a : ℝ) :
    HasExpGrowth (fun x => a * f x) := by
  obtain ⟨M, c, hM, hc, hf⟩ := hg
  refine ⟨|a| * M, c, by positivity, hc, fun x => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf x) (abs_nonneg a)

/-- Real exponential functions of linear arguments have at most exponential growth. -/
theorem HasExpGrowth.exp_linear (a : ℝ) : HasExpGrowth (fun x : ℝ => exp (a * x)) := by
  refine ⟨1, |a|, by norm_num, abs_nonneg a, fun x => ?_⟩
  rw [abs_of_pos (exp_pos _), one_mul]
  exact exp_le_exp.mpr ((le_abs_self (a * x)).trans_eq (abs_mul a x))

/-- Completing the square absorbs linear exponential growth into half the Gaussian decay. -/
theorem exp_neg_sq_add_abs_le {a : ℝ} (ha : 0 < a) (c y : ℝ) :
    exp (-a * y ^ 2 + c * |y|) ≤
      exp (c ^ 2 / (2 * a)) * exp (-(a / 2) * y ^ 2) := by
  rw [← exp_add]
  apply exp_le_exp.mpr
  have h : c * |y| ≤ a / 2 * y ^ 2 + c ^ 2 / (2 * a) := by
    calc
      _ ≤ (a ^ 2 * y ^ 2 + c ^ 2) / (2 * a) := by
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith [sq_nonneg (a * |y| - c), sq_abs y]
      _ = _ := by field_simp
  linarith

/-- Every polynomial moment remains integrable after a linear exponential weight. -/
theorem integrable_pow_mul_exp_neg_sq_add_abs {a : ℝ} (ha : 0 < a) (c : ℝ) (n : ℕ) :
    Integrable (fun y : ℝ => |y| ^ n * exp (-a * y ^ 2 + c * |y|)) := by
  have hi := (integrable_rpow_mul_exp_neg_mul_sq (by positivity : 0 < a / 2)
    (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n) : (-1 : ℝ) < (n : ℝ))).norm
  simp only [rpow_natCast, Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (exp_pos _)] at hi
  apply (hi.const_mul (exp (c ^ 2 / (2 * a)))).mono' (by fun_prop)
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ |y| ^ n * (exp (c ^ 2 / (2 * a)) * exp (-(a / 2) * y ^ 2)) :=
      mul_le_mul_of_nonneg_left (exp_neg_sq_add_abs_le ha c y) (by positivity)
    _ = _ := by ring

/-- Gaussian damping turns any exponentially growing datum into bounded data. -/
theorem HasExpGrowth.gaussian_damped_bounded {f : ℝ → ℝ} (hg : HasExpGrowth f)
    {a : ℝ} (ha : 0 < a) : ∃ M, ∀ y, |exp (-a * y ^ 2) * f y| ≤ M := by
  obtain ⟨M, c, hM, _, hf⟩ := hg
  refine ⟨M * exp (c ^ 2 / (2 * a)), fun y => ?_⟩
  rw [abs_mul, abs_of_pos (exp_pos _)]
  calc
    _ ≤ exp (-a * y ^ 2) * (M * exp (c * |y|)) :=
      mul_le_mul_of_nonneg_left (hf y) (exp_pos _).le
    _ = M * exp (-a * y ^ 2 + c * |y|) := by rw [exp_add]; ring
    _ ≤ M * (exp (c ^ 2 / (2 * a)) * exp (-(a / 2) * y ^ 2)) :=
      mul_le_mul_of_nonneg_left (exp_neg_sq_add_abs_le ha c y) hM
    _ ≤ M * exp (c ^ 2 / (2 * a)) := by
      have he : exp (-(a / 2) * y ^ 2) ≤ 1 := exp_le_one_iff.mpr (by nlinarith [sq_nonneg y])
      nlinarith [mul_nonneg hM (exp_pos (c ^ 2 / (2 * a))).le]

/-- Uniform exponential control after bounded affine shifts, useful for rescaled kernels. -/
theorem HasExpGrowth.affine_bound {f : ℝ → ℝ} (hg : HasExpGrowth f)
    (R S : ℝ) : ∃ A c : ℝ, 0 ≤ A ∧ 0 ≤ c ∧ ∀ z s y,
      |z| ≤ R → |s| ≤ S → |f (z - s * y)| ≤ A * exp (c * |y|) := by
  obtain ⟨M, c, hM, hc, hf⟩ := hg
  refine ⟨M * exp (c * R), c * max S 0, by positivity, mul_nonneg hc (le_max_right _ _), ?_⟩
  intro z s y hz hs
  have hab : |z - s * y| ≤ R + max S 0 * |y| :=
    (abs_sub _ _).trans (add_le_add hz (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hs.trans (le_max_left _ _)) (abs_nonneg _)))
  calc
    _ ≤ M * exp (c * |z - s * y|) := hf _
    _ ≤ M * exp (c * (R + max S 0 * |y|)) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hc)) hM
    _ = _ := by simp only [mul_add, exp_add, mul_assoc]

namespace GaussianMoments

/-- Damping the datum by `exp (-a * y ^ 2)` shifts the Gaussian parameter by `a`: for
`f : ℝ → ℝ`, `n : ℕ`, `a : ℝ` and `p : ℝ × ℝ`, multiplying `f y` by `exp (-a * y ^ 2)` leaves
the moment unchanged when the parameter changes from `(p.1, p.2)` to `(p.1 - a, p.2)`:
`gaussianMoment f n p` equals
`gaussianMoment (fun y => exp (-a * y ^ 2) * f y) n (p.1 - a, p.2)`, where
`gaussianMoment f n p = ∫ y, y ^ n * exp (-p.1 * y ^ 2 + p.2 * y) * f y`. -/
theorem gaussianMoment_damped (f : ℝ → ℝ) (n : ℕ) (a : ℝ) (p : ℝ × ℝ) :
    gaussianMoment f n p =
      gaussianMoment (fun y => exp (-a * y ^ 2) * f y) n (p.1 - a, p.2) := by
  apply integral_congr_ae
  filter_upwards with y
  have he : exp (-p.1 * y ^ 2 + p.2 * y) =
      exp (-(p.1 - a) * y ^ 2 + p.2 * y) * exp (-a * y ^ 2) := by
    rw [← exp_add]
    congr 1
    ring
  change y ^ n * exp (-p.1 * y ^ 2 + p.2 * y) * f y = _
  rw [he]
  ring

/-- Polynomial Gaussian moments are integrable for exponentially growing measurable data. -/
theorem integrable_gaussianMoment_of_exp_growth {f : ℝ → ℝ} (hf : AEStronglyMeasurable f)
    (hg : HasExpGrowth f) (n : ℕ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    Integrable (fun y => y ^ n * exp (-p.1 * y ^ 2 + p.2 * y) * f y) := by
  let g := fun y => exp (-(p.1 / 2) * y ^ 2) * f y
  have hm : AEStronglyMeasurable g := (by fun_prop : Continuous
    (fun y : ℝ => exp (-(p.1 / 2) * y ^ 2))).aestronglyMeasurable.mul hf
  have hi := integrable_gaussianMoment hm (hg.gaussian_damped_bounded (by positivity)) n
    (p := (p.1 - p.1 / 2, p.2)) (by dsimp; linarith)
  convert hi using 1
  funext y
  dsimp [g]
  have he : exp (-p.1 * y ^ 2 + p.2 * y) =
      exp (-(p.1 - p.1 / 2) * y ^ 2 + p.2 * y) * exp (-(p.1 / 2) * y ^ 2) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he]
  ring

/-- Joint moment derivatives retain the same recurrence for exponential growth. -/
theorem gaussianMoment_hasFDerivAt_of_exp_growth {f : ℝ → ℝ} (hf : AEStronglyMeasurable f)
    (hg : HasExpGrowth f) (n : ℕ) {p : ℝ × ℝ} (hp : 0 < p.1) :
    HasFDerivAt (gaussianMoment f n)
      ((-gaussianMoment f (n + 2) p) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        gaussianMoment f (n + 1) p • ContinuousLinearMap.snd ℝ ℝ ℝ) p := by
  let a := p.1 / 2
  let g := fun y => exp (-a * y ^ 2) * f y
  have hm : AEStronglyMeasurable g := (by fun_prop : Continuous
    (fun y : ℝ => exp (-a * y ^ 2))).aestronglyMeasurable.mul hf
  have hs : HasFDerivAt (fun q : ℝ × ℝ => (q.1 - a, q.2))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
    simpa using! ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).sub_const a).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  have hd := (gaussianMoment_hasFDerivAt hm (hg.gaussian_damped_bounded (by dsimp [a]; positivity))
    n (p := (p.1 - a, p.2)) (by dsimp [a]; linarith)).comp p
    hs
  have hid : (ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ) =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by ext <;> rfl
  rw [hid, ContinuousLinearMap.comp_id] at hd
  simpa only [g, Function.comp_def, ← gaussianMoment_damped] using! hd

/-- Every Gaussian moment is jointly smooth on positive decay, with exponential data. -/
theorem gaussianMoment_contDiffOn_of_exp_growth {f : ℝ → ℝ} (hf : AEStronglyMeasurable f)
    (hg : HasExpGrowth f) (n : ℕ) :
    ContDiffOn ℝ ∞ (gaussianMoment f n) (Ioi 0 ×ˢ univ) := by
  intro p hp
  let a := p.1 / 2
  let g := fun y => exp (-a * y ^ 2) * f y
  have hm : AEStronglyMeasurable g := (by fun_prop : Continuous
    (fun y : ℝ => exp (-a * y ^ 2))).aestronglyMeasurable.mul hf
  have ha : 0 < a := half_pos hp.1
  have hpa : 0 < p.1 - a := by dsimp [a]; linarith [show 0 < p.1 from hp.1]
  have hc : ContDiffAt ℝ ∞ (gaussianMoment g n) (p.1 - a, p.2) :=
    (gaussianMoment_contDiffOn hm (hg.gaussian_damped_bounded ha) n).contDiffAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds
        (show (p.1 - a, p.2) ∈ Ioi (0 : ℝ) ×ˢ univ from ⟨hpa, mem_univ _⟩))
  have hc' := hc.comp p (show ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => (q.1 - a, q.2)) p by fun_prop)
  have he : gaussianMoment f n = fun q : ℝ × ℝ => gaussianMoment g n (q.1 - a, q.2) :=
    funext (gaussianMoment_damped f n a)
  rw [he]
  exact hc'.contDiffWithinAt

end GaussianMoments
end MathlibExt.Analysis
