/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Trade.StolperSamuelson
import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

open scoped Topology

namespace MathlibExtTest.Economics.Trade.StolperSamuelson

-- Test section: fixed-coefficient instance with `aL₁ = 2, aK₁ = 1, aL₂ = 1, aK₂ = 2`,
-- `c₁ x = x.1 * 2 + x.2 * 1`, `c₂ x = x.1 * 1 + x.2 * 2`,
-- `f p = ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3)`, `p₀ = (3, 3)`, `f p₀ = (1, 1)`.

/-- Good 1 cost-minimizing bundle at `(1, 1)`. -/
example : MathlibExt.Economics.StolperSamuelson.IsCostMinimizingAt
    (fun x : ℝ × ℝ => x.1 * 2 + x.2 * 1) 2 1 (1, 1) :=
  { le_bundle_cost := Filter.Eventually.of_forall fun _ => le_refl _
    eq_bundle_cost := rfl }

/-- Good 2 cost-minimizing bundle at `(1, 1)`. -/
example : MathlibExt.Economics.StolperSamuelson.IsCostMinimizingAt
    (fun x : ℝ × ℝ => x.1 * 1 + x.2 * 2) 1 2 (1, 1) :=
  { le_bundle_cost := Filter.Eventually.of_forall fun _ => le_refl _
    eq_bundle_cost := rfl }

/-- Zero-profit identities hold for every `p`. -/
example (p : ℝ × ℝ) :
    (fun x : ℝ × ℝ => x.1 * 2 + x.2 * 1)
        ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3) = p.1 ∧
    (fun x : ℝ × ℝ => x.1 * 1 + x.2 * 2)
        ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3) = p.2 := by
  constructor
  · show ((2 * p.1 - p.2) / 3) * 2 + ((2 * p.2 - p.1) / 3) * 1 = p.1
    ring
  · show ((2 * p.1 - p.2) / 3) * 1 + ((2 * p.2 - p.1) / 3) * 2 = p.2
    ring

/-- Factor-price response to `p₁` in the fixed-coefficient instance. -/
example : fderiv ℝ (fun p : ℝ × ℝ => ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3))
    (3, 3) (1, 0) = (2 / 3, -1 / 3) := by
  have hsub1 : HasFDerivAt (fun p : ℝ × ℝ => 2 * p.1 - p.2)
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ) (3, 3) :=
    (hasFDerivAt_fst.const_mul (2 : ℝ)).sub hasFDerivAt_snd
  have hL1 : HasFDerivAt (fun p : ℝ × ℝ => (2 * p.1 - p.2) / 3)
      ((3⁻¹ : ℝ) • ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ))
      (3, 3) := by
    have h := hsub1.const_mul (3⁻¹ : ℝ)
    apply h.congr_of_eventuallyEq
    filter_upwards with p
    ring
  have hsub2 : HasFDerivAt (fun p : ℝ × ℝ => 2 * p.2 - p.1)
      ((2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ) (3, 3) :=
    (hasFDerivAt_snd.const_mul (2 : ℝ)).sub hasFDerivAt_fst
  have hL2 : HasFDerivAt (fun p : ℝ × ℝ => (2 * p.2 - p.1) / 3)
      ((3⁻¹ : ℝ) • ((2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ))
      (3, 3) := by
    have h := hsub2.const_mul (3⁻¹ : ℝ)
    apply h.congr_of_eventuallyEq
    filter_upwards with p
    ring
  have hfderiv : HasFDerivAt (fun p : ℝ × ℝ => ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3))
      (((3⁻¹ : ℝ) • ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
        ((3⁻¹ : ℝ) • ((2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ)))
      (3, 3) :=
    hL1.prodMk hL2
  have hfd := hfderiv.fderiv
  rw [hfd]
  simp only [ContinuousLinearMap.prod_apply, sub_apply, smul_apply, smul_eq_mul]
  show ((3⁻¹ : ℝ) * (2 * (1 : ℝ) - 0), (3⁻¹ : ℝ) * (2 * (0 : ℝ) - 1)) = (2 / 3, -1 / 3)
  rw [Prod.mk.injEq]
  constructor <;> norm_num

/-- Apply `wage_magnified_rental_falls` to the fixed-coefficient instance. -/
example : (1 : ℝ) < 3 * (fderiv ℝ
    (fun p : ℝ × ℝ => ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3)) (3, 3) (1, 0)).1 := by
  have hf00 : (fun p : ℝ × ℝ => ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3)) (3, 3)
      = (1, 1) := by
    show ((2 * (3, 3).1 - (3, 3).2) / 3, (2 * (3, 3).2 - (3, 3).1) / 3) = (1, 1)
    rw [Prod.mk.injEq]
    show (2 * 3 - 3) / 3 = 1 ∧ (2 * 3 - 3) / 3 = 1
    exact ⟨by norm_num, by norm_num⟩
  have hmin1 : MathlibExt.Economics.StolperSamuelson.IsCostMinimizingAt
      (fun x : ℝ × ℝ => x.1 * 2 + x.2 * 1) 2 1 (1, 1) :=
    { le_bundle_cost := Filter.Eventually.of_forall fun _ => le_refl _
      eq_bundle_cost := rfl }
  have hmin2 : MathlibExt.Economics.StolperSamuelson.IsCostMinimizingAt
      (fun x : ℝ × ℝ => x.1 * 1 + x.2 * 2) 1 2 (1, 1) :=
    { le_bundle_cost := Filter.Eventually.of_forall fun _ => le_refl _
      eq_bundle_cost := rfl }
  have h1 : MathlibExt.Economics.StolperSamuelson.IsCostMinimizingAt
      (fun x : ℝ × ℝ => x.1 * 2 + x.2 * 1) 2 1
      ((fun p : ℝ × ℝ => ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3)) (3, 3)) := by
    rw [hf00]
    exact hmin1
  have h2 : MathlibExt.Economics.StolperSamuelson.IsCostMinimizingAt
      (fun x : ℝ × ℝ => x.1 * 1 + x.2 * 2) 1 2
      ((fun p : ℝ × ℝ => ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3)) (3, 3)) := by
    rw [hf00]
    exact hmin2
  have hc1 : DifferentiableAt ℝ (fun x : ℝ × ℝ => x.1 * 2 + x.2 * 1)
      ((fun p : ℝ × ℝ => ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3)) (3, 3)) :=
    ((hasFDerivAt_fst.mul_const 2).add (hasFDerivAt_snd.mul_const 1)).differentiableAt
  have hc2 : DifferentiableAt ℝ (fun x : ℝ × ℝ => x.1 * 1 + x.2 * 2)
      ((fun p : ℝ × ℝ => ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3)) (3, 3)) :=
    ((hasFDerivAt_fst.mul_const 1).add (hasFDerivAt_snd.mul_const 2)).differentiableAt
  have hsub1 : HasFDerivAt (fun p : ℝ × ℝ => 2 * p.1 - p.2)
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ) (3, 3) :=
    (hasFDerivAt_fst.const_mul (2 : ℝ)).sub hasFDerivAt_snd
  have hL1 : HasFDerivAt (fun p : ℝ × ℝ => (2 * p.1 - p.2) / 3)
      ((3⁻¹ : ℝ) • ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ))
      (3, 3) := by
    have h := hsub1.const_mul (3⁻¹ : ℝ)
    apply h.congr_of_eventuallyEq
    filter_upwards with p
    ring
  have hsub2 : HasFDerivAt (fun p : ℝ × ℝ => 2 * p.2 - p.1)
      ((2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ) (3, 3) :=
    (hasFDerivAt_snd.const_mul (2 : ℝ)).sub hasFDerivAt_fst
  have hL2 : HasFDerivAt (fun p : ℝ × ℝ => (2 * p.2 - p.1) / 3)
      ((3⁻¹ : ℝ) • ((2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ))
      (3, 3) := by
    have h := hsub2.const_mul (3⁻¹ : ℝ)
    apply h.congr_of_eventuallyEq
    filter_upwards with p
    ring
  have hfderiv : HasFDerivAt (fun p : ℝ × ℝ => ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3))
      (((3⁻¹ : ℝ) • ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ - ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
        ((3⁻¹ : ℝ) • ((2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ - ContinuousLinearMap.fst ℝ ℝ ℝ)))
      (3, 3) :=
    hL1.prodMk hL2
  have hf : DifferentiableAt ℝ
      (fun p : ℝ × ℝ => ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3)) (3, 3) :=
    hfderiv.differentiableAt
  have hzero : ∀ᶠ p in 𝓝 (3, 3),
      (fun x : ℝ × ℝ => x.1 * 2 + x.2 * 1)
          ((fun p : ℝ × ℝ => ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3)) p) = p.1 ∧
      (fun x : ℝ × ℝ => x.1 * 1 + x.2 * 2)
          ((fun p : ℝ × ℝ => ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3)) p) = p.2 := by
    filter_upwards with p
    constructor
    · show ((2 * p.1 - p.2) / 3) * 2 + ((2 * p.2 - p.1) / 3) * 1 = p.1
      ring
    · show ((2 * p.1 - p.2) / 3) * 1 + ((2 * p.2 - p.1) / 3) * 2 = p.2
      ring
  have hw : 0 < ((fun p : ℝ × ℝ => ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3))
      (3, 3)).1 := by
    rw [hf00]
    show (0 : ℝ) < 1
    norm_num
  have hr : 0 < ((fun p : ℝ × ℝ => ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3))
      (3, 3)).2 := by
    rw [hf00]
    show (0 : ℝ) < 1
    norm_num
  have hmain := MathlibExt.Economics.StolperSamuelson.wage_magnified_rental_falls
    h1 h2 hc1 hc2 hf hzero hw hr
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (1 : ℝ) * 1 < 2 * 2)
  have hfd := hfderiv.fderiv
  have hval1 : (fderiv ℝ (fun p : ℝ × ℝ => ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3))
      (3, 3) (1, 0)).1 = 2 / 3 := by
    rw [hfd]
    simp only [ContinuousLinearMap.prod_apply, sub_apply, smul_apply, smul_eq_mul]
    show (3⁻¹ : ℝ) * (2 * (1 : ℝ) - 0) = 2 / 3
    norm_num
  have hnum : (3 : ℝ) * (2 / 3) = 2 := by norm_num
  have hconcl : (1 : ℝ) < 3 * (2 / 3) := by
    have h := hmain.1
    rw [hval1] at h
    have h' : ((fun p : ℝ × ℝ => ((2 * p.1 - p.2) / 3, (2 * p.2 - p.1) / 3))
        (3, 3)).1 < (3, 3).1 * (2 / 3) := h
    rw [hf00] at h'
    simpa using h'
  rw [hnum] at hconcl
  rw [hval1, hnum]
  exact hconcl

end MathlibExtTest.Economics.Trade.StolperSamuelson
