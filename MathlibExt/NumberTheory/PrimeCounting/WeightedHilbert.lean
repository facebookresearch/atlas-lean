/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Weighted Hilbert inequality

The weighted cosecant form used in the Montgomery–Vaughan proof of the
Brun–Titchmarsh theorem.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeCounting

open Set MeasureTheory

private theorem convex_midpoint_mul_le_integral (g : ℝ → ℝ) {A B c w : ℝ}
    (hw : 0 < w) (hg : ConvexOn ℝ (Icc A B) g)
    (hgc : ContinuousOn g (Icc A B))
    (hsub : Icc (c - w / 2) (c + w / 2) ⊆ Icc A B) :
    w * g c ≤ ∫ x in Ioc (c - w / 2) (c + w / 2), g x := by
  have hId : IntegrableOn (fun x : ℝ => x)
      (Ioc (c - w / 2) (c + w / 2)) volume :=
    (continuous_id.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have hInt : IntegrableOn (g ∘ fun x : ℝ => x)
      (Ioc (c - w / 2) (c + w / 2)) volume := by
    change IntegrableOn g (Ioc (c - w / 2) (c + w / 2)) volume
    exact (hgc.mono hsub).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hJ := hg.map_set_average_le hgc isClosed_Icc
    (show volume (Ioc (c - w / 2) (c + w / 2)) ≠ 0 by
      rw [Real.volume_Ioc]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith)))
    (show volume (Ioc (c - w / 2) (c + w / 2)) ≠ ⊤ by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hsub ⟨hx.1.le, hx.2⟩)
    hId hInt
  have hAvgId :
      (⨍ x in Ioc (c - w / 2) (c + w / 2), x ∂volume) = c := by
    rw [average_eq]
    simp only [MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
      Real.volume_real_Ioc, add_sub_sub_cancel, add_halves, smul_eq_mul]
    rw [max_eq_left hw.le]
    rw [← intervalIntegral.integral_of_le (by linarith), integral_id]
    field_simp
    ring
  have hAvgG :
      (⨍ x in Ioc (c - w / 2) (c + w / 2), g x ∂volume) =
        (1 / w) * ∫ x in Ioc (c - w / 2) (c + w / 2), g x := by
    rw [average_eq]
    simp [hw.le]
  simp only [hAvgId, hAvgG] at hJ
  calc
    w * g c ≤ w * ((1 / w) *
        ∫ x in Ioc (c - w / 2) (c + w / 2), g x) :=
      mul_le_mul_of_nonneg_left hJ hw.le
    _ = ∫ x in Ioc (c - w / 2) (c + w / 2), g x := by
      field_simp

private theorem convex_packed_sum_le_integral {ι : Type*} [Fintype ι]
    (g : ℝ → ℝ) (c w : ι → ℝ) {A B : ℝ}
    (hAB : A ≤ B) (hw : ∀ i, 0 < w i)
    (hleft : ∀ i, A ≤ c i - w i / 2)
    (hright : ∀ i, c i + w i / 2 ≤ B)
    (hsep : ∀ i j, i ≠ j → (w i + w j) / 2 ≤ |c i - c j|)
    (hg : ConvexOn ℝ (Icc A B) g) (hgc : ContinuousOn g (Icc A B))
    (hgnonneg : ∀ y ∈ Icc A B, 0 ≤ g y) :
    ∑ i, w i * g (c i) ≤ ∫ y in A..B, g y := by
  classical
  let J : ι → Set ℝ := fun i => Ioc (c i - w i / 2) (c i + w i / 2)
  have hJsub (i : ι) : Icc (c i - w i / 2) (c i + w i / 2) ⊆ Icc A B := by
    intro y hy
    exact ⟨(hleft i).trans hy.1, hy.2.trans (hright i)⟩
  have hmid (i : ι) :
      w i * g (c i) ≤ ∫ y in J i, g y := by
    exact convex_midpoint_mul_le_integral g (hw i) hg hgc (hJsub i)
  have hdis : Set.Pairwise (Set.univ : Set ι) (Function.onFun Disjoint J) := by
    intro i _ j _ hij
    change Disjoint (J i) (J j)
    rw [Set.disjoint_left]
    intro y hyi hyj
    simp only [J, mem_Ioc] at hyi hyj
    have hs := hsep i j hij
    rcases le_total (c i) (c j) with hijc | hjic
    · rw [abs_of_nonpos (sub_nonpos.mpr hijc)] at hs
      have hlt : c j - c i < (w i + w j) / 2 := by linarith
      nlinarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hjic)] at hs
      have hlt : c i - c j < (w i + w j) / 2 := by linarith
      exact (not_lt_of_ge hs hlt)
  have hJint (i : ι) : IntegrableOn g (J i) volume :=
    ((hgc.mono (hJsub i)).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have hUnionSub : (⋃ i, J i) ⊆ Ioc A B := by
    intro y hy
    simp only [mem_iUnion] at hy
    obtain ⟨i, hyi⟩ := hy
    simp only [J, mem_Ioc] at hyi
    exact ⟨lt_of_le_of_lt (hleft i) hyi.1, hyi.2.trans (hright i)⟩
  have hBigInt : IntegrableOn g (Ioc A B) volume :=
    (hgc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  calc
    ∑ i, w i * g (c i) ≤ ∑ i, ∫ y in J i, g y :=
      Finset.sum_le_sum fun i _ => hmid i
    _ = ∫ y in ⋃ i, J i, g y := by
      rw [MeasureTheory.integral_iUnion_fintype]
      · exact fun i => measurableSet_Ioc
      · simpa only [Set.pairwise_univ] using hdis
      · exact hJint
    _ ≤ ∫ y in Ioc A B, g y := by
      apply MeasureTheory.setIntegral_mono_set hBigInt
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        exact hgnonneg y ⟨hy.1.le, hy.2⟩
      · exact Filter.Eventually.of_forall hUnionSub
    _ = ∫ y in A..B, g y := (intervalIntegral.integral_of_le hAB).symm

private noncomputable def cscSq (y : ℝ) : ℝ :=
  1 / Real.sin (Real.pi * y) ^ 2

private noncomputable def cscSqDeriv (y : ℝ) : ℝ :=
  -2 * Real.pi * Real.cos (Real.pi * y) / Real.sin (Real.pi * y) ^ 3

private noncomputable def cscSqDeriv2 (y : ℝ) : ℝ :=
  2 * Real.pi ^ 2 * (1 + 2 * Real.cos (Real.pi * y) ^ 2) /
    Real.sin (Real.pi * y) ^ 4

private theorem sin_pi_mul_pos {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    0 < Real.sin (Real.pi * y) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · nlinarith [Real.pi_pos]

private theorem hasDerivAt_cscSq {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt cscSq (cscSqDeriv y) y := by
  have harg : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi y := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul Real.pi
  have hs := harg.sin
  have hspow := hs.pow 2
  have hne : Real.sin (Real.pi * y) ^ 2 ≠ 0 := by
    exact pow_ne_zero _ (ne_of_gt (sin_pi_mul_pos hy0 hy1))
  have hquot := (hasDerivAt_const y (1 : ℝ)).div hspow hne
  convert hquot using 1
  · ext t
    rfl
  · simp only [cscSqDeriv, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, one_mul, zero_mul, zero_sub]
    field_simp [ne_of_gt (sin_pi_mul_pos hy0 hy1)]

private theorem hasDerivAt_cscSqDeriv {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt cscSqDeriv (cscSqDeriv2 y) y := by
  have harg : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi y := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul Real.pi
  have hs := harg.sin
  have hc := harg.cos
  have hnum := hc.const_mul (-2 * Real.pi)
  have hden := hs.pow 3
  have hne : Real.sin (Real.pi * y) ^ 3 ≠ 0 := by
    exact pow_ne_zero _ (ne_of_gt (sin_pi_mul_pos hy0 hy1))
  have hquot := hnum.div hden hne
  convert hquot using 1
  · ext t
    rfl
  · simp only [cscSqDeriv2, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub,
      pow_two]
    field_simp [ne_of_gt (sin_pi_mul_pos hy0 hy1)]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * y)]

private theorem hasDerivAt_cscSq_of_sin_ne {y : ℝ}
    (hne : Real.sin (Real.pi * y) ≠ 0) :
    HasDerivAt cscSq (cscSqDeriv y) y := by
  have harg : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi y := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul Real.pi
  have hs := harg.sin
  have hspow := hs.pow 2
  have hquot := (hasDerivAt_const y (1 : ℝ)).div hspow (pow_ne_zero _ hne)
  convert hquot using 1
  · ext t
    rfl
  · simp only [cscSqDeriv, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub,
      pow_one, one_mul, zero_mul, zero_sub]
    field_simp [hne]

private theorem hasDerivAt_cscSqDeriv_of_sin_ne {y : ℝ}
    (hne : Real.sin (Real.pi * y) ≠ 0) :
    HasDerivAt cscSqDeriv (cscSqDeriv2 y) y := by
  have harg : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi y := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul Real.pi
  have hs := harg.sin
  have hc := harg.cos
  have hnum := hc.const_mul (-2 * Real.pi)
  have hden := hs.pow 3
  have hquot := hnum.div hden (pow_ne_zero _ hne)
  convert hquot using 1
  · ext t
    rfl
  · simp only [cscSqDeriv2, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub,
      pow_two]
    field_simp [hne]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * y)]

private theorem cscSq_continuousOn {A B : ℝ} (hA : 0 < A) (hB : B < 1) :
    ContinuousOn cscSq (Icc A B) := by
  intro y hy
  exact (hasDerivAt_cscSq (hA.trans_le hy.1) (hy.2.trans_lt hB)).continuousAt.continuousWithinAt

private theorem cscSq_convexOn {A B : ℝ} (hA : 0 < A) (hB : B < 1) :
    ConvexOn ℝ (Icc A B) cscSq := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc A B)
    (cscSq_continuousOn hA hB)
  · intro y hy
    have hy' := interior_subset hy
    exact (hasDerivAt_cscSq (hA.trans_le hy'.1) (hy'.2.trans_lt hB)).hasDerivWithinAt
  · intro y hy
    have hy' := interior_subset hy
    exact (hasDerivAt_cscSqDeriv
      (hA.trans_le hy'.1) (hy'.2.trans_lt hB)).hasDerivWithinAt
  · intro y hy
    have hy' := interior_subset hy
    have hsin := sin_pi_mul_pos (hA.trans_le hy'.1) (hy'.2.trans_lt hB)
    simp only [cscSqDeriv2]
    positivity

private noncomputable def cscSqProduct (a y : ℝ) : ℝ :=
  cscSq y * cscSq (y - a)

private noncomputable def cscSqProductDeriv (a y : ℝ) : ℝ :=
  cscSqDeriv y * cscSq (y - a) + cscSq y * cscSqDeriv (y - a)

private noncomputable def cscSqProductDeriv2 (a y : ℝ) : ℝ :=
  cscSqDeriv2 y * cscSq (y - a) +
    2 * cscSqDeriv y * cscSqDeriv (y - a) +
    cscSq y * cscSqDeriv2 (y - a)

private theorem hasDerivAt_cscSqProduct {a y : ℝ}
    (hy : Real.sin (Real.pi * y) ≠ 0)
    (hya : Real.sin (Real.pi * (y - a)) ≠ 0) :
    HasDerivAt (cscSqProduct a) (cscSqProductDeriv a y) y := by
  have hshift : HasDerivAt (fun t : ℝ => t - a) 1 y := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id y).sub_const a
  have hu := hasDerivAt_cscSq_of_sin_ne hy
  have hv : HasDerivAt (fun t : ℝ => cscSq (t - a)) (cscSqDeriv (y - a)) y := by
    convert (hasDerivAt_cscSq_of_sin_ne hya).comp y hshift using 1
    · ext t
      rfl
    · ring
  convert hu.mul hv using 1
  · ext t
    rfl
  · rfl

private theorem hasDerivAt_cscSqProductDeriv {a y : ℝ}
    (hy : Real.sin (Real.pi * y) ≠ 0)
    (hya : Real.sin (Real.pi * (y - a)) ≠ 0) :
    HasDerivAt (cscSqProductDeriv a) (cscSqProductDeriv2 a y) y := by
  have hshift : HasDerivAt (fun t : ℝ => t - a) 1 y := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id y).sub_const a
  have hu := hasDerivAt_cscSq_of_sin_ne hy
  have hdu := hasDerivAt_cscSqDeriv_of_sin_ne hy
  have hv : HasDerivAt (fun t : ℝ => cscSq (t - a)) (cscSqDeriv (y - a)) y := by
    convert (hasDerivAt_cscSq_of_sin_ne hya).comp y hshift using 1
    · ext t
      rfl
    · ring
  have hdv : HasDerivAt (fun t : ℝ => cscSqDeriv (t - a))
      (cscSqDeriv2 (y - a)) y := by
    convert (hasDerivAt_cscSqDeriv_of_sin_ne hya).comp y hshift using 1
    · ext t
      rfl
    · ring
  convert (hdu.mul hv).add (hu.mul hdv) using 1
  · ext t
    simp only [cscSqProductDeriv, Pi.add_apply, Pi.mul_apply]
  · simp only [cscSqProductDeriv2]
    ring

private theorem cscSqProductDeriv2_nonneg {a y : ℝ}
    (hy : Real.sin (Real.pi * y) ≠ 0)
    (hya : Real.sin (Real.pi * (y - a)) ≠ 0) :
    0 ≤ cscSqProductDeriv2 a y := by
  let s₁ := Real.sin (Real.pi * y)
  let c₁ := Real.cos (Real.pi * y)
  let s₂ := Real.sin (Real.pi * (y - a))
  let c₂ := Real.cos (Real.pi * (y - a))
  have hs₁ : s₁ ≠ 0 := hy
  have hs₂ : s₂ ≠ 0 := hya
  have hs₁4 : 0 < s₁ ^ 4 := (by norm_num : Even 4).pow_pos hs₁
  have hs₂4 : 0 < s₂ ^ 4 := (by norm_num : Even 4).pow_pos hs₂
  have hden : 0 < s₁ ^ 4 * s₂ ^ 4 := mul_pos hs₁4 hs₂4
  rw [show cscSqProductDeriv2 a y =
      2 * Real.pi ^ 2 /
        (s₁ ^ 4 * s₂ ^ 4) *
          (s₁ ^ 2 + s₂ ^ 2 + 2 * (c₁ * s₂ + c₂ * s₁) ^ 2) by
    simp only [cscSqProductDeriv2, cscSqDeriv2, cscSqDeriv, cscSq,
      s₁, c₁, s₂, c₂]
    field_simp [hs₁, hs₂]
    ring]
  positivity

private theorem cscSqProduct_convexOn {a A B : ℝ}
    (hy : ∀ y ∈ Icc A B, Real.sin (Real.pi * y) ≠ 0)
    (hya : ∀ y ∈ Icc A B, Real.sin (Real.pi * (y - a)) ≠ 0) :
    ConvexOn ℝ (Icc A B) (cscSqProduct a) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc A B)
  · intro y hyI
    exact (hasDerivAt_cscSqProduct (hy y hyI) (hya y hyI)).continuousAt.continuousWithinAt
  · intro y hyI
    have hyI' := interior_subset hyI
    exact (hasDerivAt_cscSqProduct
      (hy y hyI') (hya y hyI')).hasDerivWithinAt
  · intro y hyI
    have hyI' := interior_subset hyI
    exact (hasDerivAt_cscSqProductDeriv
      (hy y hyI') (hya y hyI')).hasDerivWithinAt
  · intro y hyI
    have hyI' := interior_subset hyI
    exact cscSqProductDeriv2_nonneg (hy y hyI') (hya y hyI')

private theorem cscSqProduct_continuousOn {a A B : ℝ}
    (hy : ∀ y ∈ Icc A B, Real.sin (Real.pi * y) ≠ 0)
    (hya : ∀ y ∈ Icc A B, Real.sin (Real.pi * (y - a)) ≠ 0) :
    ContinuousOn (cscSqProduct a) (Icc A B) := by
  intro y hyI
  exact (hasDerivAt_cscSqProduct (hy y hyI) (hya y hyI)).continuousAt.continuousWithinAt

private noncomputable def cotPi (y : ℝ) : ℝ :=
  Real.cos (Real.pi * y) / Real.sin (Real.pi * y)

private noncomputable def logAbsSinPi (y : ℝ) : ℝ :=
  Real.log |Real.sin (Real.pi * y)|

private theorem hasDerivAt_cotPi_of_sin_ne {y : ℝ}
    (hne : Real.sin (Real.pi * y) ≠ 0) :
    HasDerivAt cotPi (-Real.pi * cscSq y) y := by
  have harg : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi y := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul Real.pi
  have hquot := harg.cos.div harg.sin hne
  convert hquot using 1
  · ext t
    rfl
  · simp only [cscSq]
    field_simp [hne]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * y)]

private theorem hasDerivAt_logAbsSinPi_of_sin_ne {y : ℝ}
    (hne : Real.sin (Real.pi * y) ≠ 0) :
    HasDerivAt logAbsSinPi (Real.pi * cotPi y) y := by
  have harg : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi y := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul Real.pi
  have hs := harg.sin
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have habs := (hs.hasFDerivAt.abs_of_neg hneg).hasDerivAt
    have hlog := habs.log (abs_ne_zero.mpr hne)
    convert hlog using 1
    · ext t
      rfl
    · simp only [cotPi, abs_of_neg hneg]
      field_simp [hne]
      simp [ContinuousLinearMap.toSpanSingleton_apply]
  · have habs := (hs.hasFDerivAt.abs_of_pos hpos).hasDerivAt
    have hlog := habs.log (abs_ne_zero.mpr hne)
    convert hlog using 1
    · ext t
      rfl
    · simp only [cotPi, abs_of_pos hpos]
      field_simp [hne]
      simp [ContinuousLinearMap.toSpanSingleton_apply]

private noncomputable def cscSqProductAnti (a y : ℝ) : ℝ :=
  cscSq a / Real.pi *
    (-cotPi y - cotPi (y - a) +
      2 * cotPi a * (logAbsSinPi y - logAbsSinPi (y - a)))

private theorem cscSqProduct_identity {a y : ℝ}
    (ha : Real.sin (Real.pi * a) ≠ 0)
    (hy : Real.sin (Real.pi * y) ≠ 0)
    (hya : Real.sin (Real.pi * (y - a)) ≠ 0) :
    cscSqProduct a y = cscSq a *
      (cscSq y + cscSq (y - a) +
        2 * cotPi a * (cotPi y - cotPi (y - a))) := by
  have hdiff :
      Real.sin (Real.pi * (y - a)) * Real.cos (Real.pi * y) -
        Real.sin (Real.pi * y) * Real.cos (Real.pi * (y - a)) =
          -Real.sin (Real.pi * a) := by
    calc
      _ = Real.sin (Real.pi * (y - a) - Real.pi * y) := by
        rw [Real.sin_sub]
        ring
      _ = Real.sin (-Real.pi * a) := by congr 1; ring
      _ = -Real.sin (Real.pi * a) := by
        rw [show -Real.pi * a = -(Real.pi * a) by ring, Real.sin_neg]
  have hcosA :
      1 - Real.cos (Real.pi * a) ^ 2 = Real.sin (Real.pi * a) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * a)]
  have hunitB :
      Real.cos (Real.pi * (y - a)) ^ 2 +
        Real.sin (Real.pi * (y - a)) ^ 2 = 1 := by
    simpa only [add_comm] using Real.sin_sq_add_cos_sq (Real.pi * (y - a))
  have hquad :
      Real.sin (Real.pi * (y - a)) ^ 2 + Real.sin (Real.pi * y) ^ 2 -
          2 * Real.sin (Real.pi * y) * Real.sin (Real.pi * (y - a)) *
            Real.cos (Real.pi * a) =
        Real.sin (Real.pi * a) ^ 2 := by
    calc
      _ = (Real.cos (Real.pi * (y - a)) * Real.sin (Real.pi * a)) ^ 2 +
          Real.sin (Real.pi * (y - a)) ^ 2 *
            (1 - Real.cos (Real.pi * a) ^ 2) := by
        rw [show Real.pi * y = Real.pi * (y - a) + Real.pi * a by ring,
          Real.sin_add]
        ring
      _ = (Real.cos (Real.pi * (y - a)) * Real.sin (Real.pi * a)) ^ 2 +
          Real.sin (Real.pi * (y - a)) ^ 2 * Real.sin (Real.pi * a) ^ 2 := by
        rw [hcosA]
      _ = Real.sin (Real.pi * a) ^ 2 *
          (Real.cos (Real.pi * (y - a)) ^ 2 +
            Real.sin (Real.pi * (y - a)) ^ 2) := by ring
      _ = Real.sin (Real.pi * a) ^ 2 := by rw [hunitB, mul_one]
  simp only [cscSqProduct, cscSq, cotPi]
  field_simp [ha, hy, hya]
  rw [hdiff]
  have hquadMul := congrArg
    (fun z : ℝ => Real.sin (Real.pi * a) * z) hquad
  ring_nf at hquadMul ⊢
  linarith

private theorem hasDerivAt_cscSqProductAnti {a y : ℝ}
    (ha : Real.sin (Real.pi * a) ≠ 0)
    (hy : Real.sin (Real.pi * y) ≠ 0)
    (hya : Real.sin (Real.pi * (y - a)) ≠ 0) :
    HasDerivAt (cscSqProductAnti a) (cscSqProduct a y) y := by
  have hshift : HasDerivAt (fun t : ℝ => t - a) 1 y := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id y).sub_const a
  have hcotY := hasDerivAt_cotPi_of_sin_ne hy
  have hcotShift : HasDerivAt (fun t : ℝ => cotPi (t - a))
      (-Real.pi * cscSq (y - a)) y := by
    convert (hasDerivAt_cotPi_of_sin_ne hya).comp y hshift using 1
    · ext t
      rfl
    · ring
  have hlogY := hasDerivAt_logAbsSinPi_of_sin_ne hy
  have hlogShift : HasDerivAt (fun t : ℝ => logAbsSinPi (t - a))
      (Real.pi * cotPi (y - a)) y := by
    convert (hasDerivAt_logAbsSinPi_of_sin_ne hya).comp y hshift using 1
    · ext t
      rfl
    · ring
  have hinner := (hcotY.neg.sub hcotShift).add
    ((hlogY.sub hlogShift).const_mul (2 * cotPi a))
  have hscaled := hinner.const_mul (cscSq a / Real.pi)
  convert hscaled using 1
  · ext t
    simp only [cscSqProductAnti, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  · rw [cscSqProduct_identity ha hy hya]
    field_simp [Real.pi_ne_zero]
    ring

private theorem integral_cscSqProduct {a A B : ℝ} (hAB : A ≤ B)
    (ha : Real.sin (Real.pi * a) ≠ 0)
    (hy : ∀ y ∈ Icc A B, Real.sin (Real.pi * y) ≠ 0)
    (hya : ∀ y ∈ Icc A B, Real.sin (Real.pi * (y - a)) ≠ 0) :
    ∫ y in A..B, cscSqProduct a y =
      cscSqProductAnti a B - cscSqProductAnti a A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hyI
    rw [uIcc_of_le hAB] at hyI
    exact hasDerivAt_cscSqProductAnti ha (hy y hyI) (hya y hyI)
  · have hc : ContinuousOn (cscSqProduct a) (uIcc A B) := by
      rw [uIcc_of_le hAB]
      intro y hyI
      exact (hasDerivAt_cscSqProduct (hy y hyI) (hya y hyI)).continuousAt.continuousWithinAt
    exact hc.intervalIntegrable

private theorem cotPi_neg (y : ℝ) : cotPi (-y) = -cotPi y := by
  simp only [cotPi, mul_neg, Real.cos_neg, Real.sin_neg]
  ring

private theorem cotPi_one_sub (y : ℝ) : cotPi (1 - y) = -cotPi y := by
  simp only [cotPi]
  rw [show Real.pi * (1 - y) = Real.pi - Real.pi * y by ring,
    Real.cos_pi_sub, Real.sin_pi_sub]
  ring

private theorem logAbsSinPi_neg (y : ℝ) : logAbsSinPi (-y) = logAbsSinPi y := by
  simp only [logAbsSinPi, mul_neg, Real.sin_neg, abs_neg]

private theorem logAbsSinPi_one_sub (y : ℝ) :
    logAbsSinPi (1 - y) = logAbsSinPi y := by
  simp only [logAbsSinPi]
  rw [show Real.pi * (1 - y) = Real.pi - Real.pi * y by ring,
    Real.sin_pi_sub]

private theorem sinPi_add_sub_diff (a g : ℝ) :
    Real.sin (Real.pi * (a + g)) - Real.sin (Real.pi * (a - g)) =
      2 * Real.cos (Real.pi * a) * Real.sin (Real.pi * g) := by
  rw [show Real.pi * (a + g) = Real.pi * a + Real.pi * g by ring,
    show Real.pi * (a - g) = Real.pi * a - Real.pi * g by ring,
    Real.sin_add, Real.sin_sub]
  ring

private theorem cotPi_antitone {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hv : v < 1) :
    cotPi v ≤ cotPi u := by
  have hsu := sin_pi_mul_pos hu (huv.trans_lt hv)
  have hsv := sin_pi_mul_pos (hu.trans_le huv) hv
  have hdiff0 : 0 ≤ Real.sin (Real.pi * (v - u)) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · positivity
    · nlinarith [Real.pi_pos]
  have hid : cotPi u - cotPi v =
      Real.sin (Real.pi * (v - u)) /
        (Real.sin (Real.pi * u) * Real.sin (Real.pi * v)) := by
    simp only [cotPi]
    field_simp [hsu.ne', hsv.ne']
    rw [show Real.pi * (v - u) = Real.pi * v - Real.pi * u by ring,
      Real.sin_sub]
    ring
  have hq : 0 ≤ Real.sin (Real.pi * (v - u)) /
      (Real.sin (Real.pi * u) * Real.sin (Real.pi * v)) := by positivity
  rw [← hid] at hq
  linarith

private theorem cotPi_half_le {d : ℝ} (hd : 0 < d) (hd1 : d < 1) :
    cotPi (d / 2) ≤ 2 / (Real.pi * d) := by
  let z : ℝ := Real.pi * (d / 2)
  have hz : 0 < z := by simp only [z]; positivity
  have hzhalf : z < Real.pi / 2 := by
    simp only [z]
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin z :=
    Real.sin_pos_of_pos_of_lt_pi hz (hzhalf.trans (by linarith [Real.pi_pos]))
  have hcos : 0 < Real.cos z :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hzhalf⟩
  have htan := Real.le_tan hz.le hzhalf
  rw [Real.tan_eq_sin_div_cos] at htan
  have hcot : Real.cos z / Real.sin z ≤ 1 / z := by
    rw [div_le_div_iff₀ hsin hz]
    simpa only [one_mul, mul_comm] using (le_div_iff₀ hcos).mp htan
  change Real.cos z / Real.sin z ≤ 2 / (Real.pi * d)
  calc
    _ ≤ 1 / z := hcot
    _ = 2 / (Real.pi * d) := by
      simp only [z]
      field_simp [Real.pi_ne_zero, hd.ne']

private theorem integral_cscSqProduct_two_arcs_le {a d e : ℝ}
    (hd : 0 < d) (he : 0 < e)
    (hleft : (d + e) / 2 ≤ a) (hright : (d + e) / 2 ≤ 1 - a) :
    (∫ y in d / 2..a - e / 2, cscSqProduct a y) +
        ∫ y in a + e / 2..1 - d / 2, cscSqProduct a y ≤
      4 / Real.pi ^ 2 * (1 / d + 1 / e) * cscSq a := by
  have hd1 : d < 1 := by linarith
  have he1 : e < 1 := by linarith
  have ha0 : 0 < a := by linarith
  have ha1 : a < 1 := by linarith
  have haSin := sin_pi_mul_pos ha0 ha1
  have hAB₁ : d / 2 ≤ a - e / 2 := by linarith
  have hAB₂ : a + e / 2 ≤ 1 - d / 2 := by linarith
  have hy₁ (y : ℝ) (hy : y ∈ Icc (d / 2) (a - e / 2)) :
      Real.sin (Real.pi * y) ≠ 0 := by
    exact (sin_pi_mul_pos (by linarith [hy.1]) (by linarith [hy.2])).ne'
  have hya₁ (y : ℝ) (hy : y ∈ Icc (d / 2) (a - e / 2)) :
      Real.sin (Real.pi * (y - a)) ≠ 0 := by
    have hs := sin_pi_mul_pos (by linarith [hy.2] : 0 < a - y)
      (by linarith [hy.1] : a - y < 1)
    rw [show Real.pi * (y - a) = -(Real.pi * (a - y)) by ring, Real.sin_neg]
    exact neg_ne_zero.mpr hs.ne'
  have hy₂ (y : ℝ) (hy : y ∈ Icc (a + e / 2) (1 - d / 2)) :
      Real.sin (Real.pi * y) ≠ 0 := by
    exact (sin_pi_mul_pos (by linarith [hy.1]) (by linarith [hy.2])).ne'
  have hya₂ (y : ℝ) (hy : y ∈ Icc (a + e / 2) (1 - d / 2)) :
      Real.sin (Real.pi * (y - a)) ≠ 0 := by
    exact (sin_pi_mul_pos (by linarith [hy.1]) (by linarith [hy.2])).ne'
  rw [integral_cscSqProduct hAB₁ haSin.ne' hy₁ hya₁,
    integral_cscSqProduct hAB₂ haSin.ne' hy₂ hya₂]
  have hEval :
      (cscSqProductAnti a (a - e / 2) - cscSqProductAnti a (d / 2)) +
          (cscSqProductAnti a (1 - d / 2) -
            cscSqProductAnti a (a + e / 2)) =
        cscSq a / Real.pi *
          (2 * cotPi (d / 2) + 2 * cotPi (e / 2) -
              cotPi (a - e / 2) - cotPi (a - d / 2) +
              cotPi (a + d / 2) + cotPi (a + e / 2) +
            2 * cotPi a *
              (logAbsSinPi (a - e / 2) + logAbsSinPi (a - d / 2) -
                logAbsSinPi (a + d / 2) - logAbsSinPi (a + e / 2))) := by
    have hcotD : cotPi (-a + d * (1 / 2)) =
        -cotPi (a + d * (-1 / 2)) := by
      rw [show -a + d * (1 / 2) = -(a + d * (-1 / 2)) by ring, cotPi_neg]
    have hlogD : logAbsSinPi (-a + d * (1 / 2)) =
        logAbsSinPi (a + d * (-1 / 2)) := by
      rw [show -a + d * (1 / 2) = -(a + d * (-1 / 2)) by ring,
        logAbsSinPi_neg]
    have hcotOne : cotPi (1 - a + d * (-1 / 2)) =
        -cotPi (a + d * (1 / 2)) := by
      rw [show 1 - a + d * (-1 / 2) = 1 - (a + d * (1 / 2)) by ring,
        cotPi_one_sub]
    have hlogOne : logAbsSinPi (1 - a + d * (-1 / 2)) =
        logAbsSinPi (a + d * (1 / 2)) := by
      rw [show 1 - a + d * (-1 / 2) = 1 - (a + d * (1 / 2)) by ring,
        logAbsSinPi_one_sub]
    simp only [cscSqProductAnti]
    rw [show a - e / 2 - a = -(e / 2) by ring,
      show d / 2 - a = -(a - d / 2) by ring,
      show 1 - d / 2 - a = 1 - (a + d / 2) by ring,
      show a + e / 2 - a = e / 2 by ring,
      cotPi_neg, cotPi_one_sub, logAbsSinPi_neg, logAbsSinPi_one_sub]
    ring_nf
    rw [hcotD, hlogD, hcotOne, hlogOne]
    ring
  rw [hEval]
  have hcotD := cotPi_antitone
    (u := a - d / 2) (v := a + d / 2)
    (by linarith) (by linarith) (by linarith)
  have hcotE := cotPi_antitone
    (u := a - e / 2) (v := a + e / 2)
    (by linarith) (by linarith) (by linarith)
  have hcotCross :
      -cotPi (a - e / 2) - cotPi (a - d / 2) +
          cotPi (a + d / 2) + cotPi (a + e / 2) ≤ 0 := by
    linarith
  have hsDm := sin_pi_mul_pos (by linarith : 0 < a - d / 2)
    (by linarith : a - d / 2 < 1)
  have hsDp := sin_pi_mul_pos (by linarith : 0 < a + d / 2)
    (by linarith : a + d / 2 < 1)
  have hsEm := sin_pi_mul_pos (by linarith : 0 < a - e / 2)
    (by linarith : a - e / 2 < 1)
  have hsEp := sin_pi_mul_pos (by linarith : 0 < a + e / 2)
    (by linarith : a + e / 2 < 1)
  have hsD := sin_pi_mul_pos (by linarith : 0 < d / 2)
    (by linarith : d / 2 < 1)
  have hsE := sin_pi_mul_pos (by linarith : 0 < e / 2)
    (by linarith : e / 2 < 1)
  let L : ℝ :=
    logAbsSinPi (a - e / 2) + logAbsSinPi (a - d / 2) -
      logAbsSinPi (a + d / 2) - logAbsSinPi (a + e / 2)
  have hlogTerm : 2 * cotPi a * L ≤ 0 := by
    by_cases hahalf : a ≤ 1 / 2
    · have hcos : 0 ≤ Real.cos (Real.pi * a) := by
        apply Real.cos_nonneg_of_mem_Icc
        constructor <;> nlinarith [Real.pi_pos]
      have hcot : 0 ≤ cotPi a := by
        simp only [cotPi]
        positivity
      have hcompD :
          Real.sin (Real.pi * (a - d / 2)) ≤
            Real.sin (Real.pi * (a + d / 2)) := by
        have hdiff := sinPi_add_sub_diff a (d / 2)
        apply sub_nonneg.mp
        rw [hdiff]
        exact mul_nonneg (mul_nonneg (by norm_num) hcos) hsD.le
      have hcompE :
          Real.sin (Real.pi * (a - e / 2)) ≤
            Real.sin (Real.pi * (a + e / 2)) := by
        have hdiff := sinPi_add_sub_diff a (e / 2)
        apply sub_nonneg.mp
        rw [hdiff]
        exact mul_nonneg (mul_nonneg (by norm_num) hcos) hsE.le
      have hlogD : logAbsSinPi (a - d / 2) ≤
          logAbsSinPi (a + d / 2) := by
        simp only [logAbsSinPi, abs_of_pos hsDm, abs_of_pos hsDp]
        exact Real.strictMonoOn_log.monotoneOn hsDm hsDp hcompD
      have hlogE : logAbsSinPi (a - e / 2) ≤
          logAbsSinPi (a + e / 2) := by
        simp only [logAbsSinPi, abs_of_pos hsEm, abs_of_pos hsEp]
        exact Real.strictMonoOn_log.monotoneOn hsEm hsEp hcompE
      have hL : L ≤ 0 := by
        simp only [L]
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by norm_num) hcot) hL
    · have hahalf' : 1 / 2 ≤ a := le_of_not_ge hahalf
      have hcos : Real.cos (Real.pi * a) ≤ 0 := by
        apply Real.cos_nonpos_of_pi_div_two_le_of_le
        · nlinarith [Real.pi_pos]
        · nlinarith [Real.pi_pos]
      have hcot : cotPi a ≤ 0 := by
        simp only [cotPi]
        exact div_nonpos_of_nonpos_of_nonneg hcos haSin.le
      have hcompD :
          Real.sin (Real.pi * (a + d / 2)) ≤
            Real.sin (Real.pi * (a - d / 2)) := by
        have hdiff := sinPi_add_sub_diff a (d / 2)
        apply sub_nonpos.mp
        rw [hdiff]
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hcos) hsD.le
      have hcompE :
          Real.sin (Real.pi * (a + e / 2)) ≤
            Real.sin (Real.pi * (a - e / 2)) := by
        have hdiff := sinPi_add_sub_diff a (e / 2)
        apply sub_nonpos.mp
        rw [hdiff]
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hcos) hsE.le
      have hlogD : logAbsSinPi (a + d / 2) ≤
          logAbsSinPi (a - d / 2) := by
        simp only [logAbsSinPi, abs_of_pos hsDp, abs_of_pos hsDm]
        exact Real.strictMonoOn_log.monotoneOn hsDp hsDm hcompD
      have hlogE : logAbsSinPi (a + e / 2) ≤
          logAbsSinPi (a - e / 2) := by
        simp only [logAbsSinPi, abs_of_pos hsEp, abs_of_pos hsEm]
        exact Real.strictMonoOn_log.monotoneOn hsEp hsEm hcompE
      have hL : 0 ≤ L := by
        simp only [L]
        linarith
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hcot) hL
  dsimp only [L] at hlogTerm
  have hinside :
      2 * cotPi (d / 2) + 2 * cotPi (e / 2) - cotPi (a - e / 2) -
            cotPi (a - d / 2) + cotPi (a + d / 2) + cotPi (a + e / 2) +
          2 * cotPi a *
            (logAbsSinPi (a - e / 2) + logAbsSinPi (a - d / 2) -
              logAbsSinPi (a + d / 2) - logAbsSinPi (a + e / 2)) ≤
        2 * cotPi (d / 2) + 2 * cotPi (e / 2) := by
    linarith
  have hcotDhalf := cotPi_half_le hd hd1
  have hcotEhalf := cotPi_half_le he he1
  have hend :
      2 * cotPi (d / 2) + 2 * cotPi (e / 2) ≤
        4 / Real.pi * (1 / d + 1 / e) := by
    calc
      _ ≤ 2 * (2 / (Real.pi * d)) + 2 * (2 / (Real.pi * e)) := by
        linarith
      _ = 4 / Real.pi * (1 / d + 1 / e) := by
        field_simp [Real.pi_ne_zero, hd.ne', he.ne']
        ring
  have hfactor : 0 ≤ cscSq a / Real.pi := by
    simp only [cscSq]
    positivity
  calc
    cscSq a / Real.pi *
        (2 * cotPi (d / 2) + 2 * cotPi (e / 2) - cotPi (a - e / 2) -
              cotPi (a - d / 2) + cotPi (a + d / 2) + cotPi (a + e / 2) +
            2 * cotPi a *
              (logAbsSinPi (a - e / 2) + logAbsSinPi (a - d / 2) -
                logAbsSinPi (a + d / 2) - logAbsSinPi (a + e / 2))) ≤
        cscSq a / Real.pi *
          (2 * cotPi (d / 2) + 2 * cotPi (e / 2)) :=
      mul_le_mul_of_nonneg_left hinside hfactor
    _ ≤ cscSq a / Real.pi * (4 / Real.pi * (1 / d + 1 / e)) :=
      mul_le_mul_of_nonneg_left hend hfactor
    _ = 4 / Real.pi ^ 2 * (1 / d + 1 / e) * cscSq a := by
      field_simp [Real.pi_ne_zero]

private noncomputable def cscSqAnti (y : ℝ) : ℝ :=
  -Real.cos (Real.pi * y) / (Real.pi * Real.sin (Real.pi * y))

private theorem hasDerivAt_cscSqAnti {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt cscSqAnti (cscSq y) y := by
  have harg : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi y := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul Real.pi
  have hs := harg.sin
  have hc := harg.cos
  have hnum := hc.neg
  have hden := hs.const_mul Real.pi
  have hne : Real.pi * Real.sin (Real.pi * y) ≠ 0 := by
    exact mul_ne_zero Real.pi_ne_zero (ne_of_gt (sin_pi_mul_pos hy0 hy1))
  have hquot := hnum.div hden hne
  convert hquot using 1
  · ext t
    rfl
  · simp only [cscSq, Pi.neg_apply]
    field_simp [Real.pi_ne_zero, ne_of_gt (sin_pi_mul_pos hy0 hy1)]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * y)]

private theorem integral_cscSq {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) (hB : B < 1) :
    ∫ y in A..B, cscSq y = cscSqAnti B - cscSqAnti A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    rw [uIcc_of_le hAB] at hy
    exact hasDerivAt_cscSqAnti (hA.trans_le hy.1) (hy.2.trans_lt hB)
  · have hc : ContinuousOn cscSq (uIcc A B) := by
      simpa only [uIcc_of_le hAB] using cscSq_continuousOn hA hB
    exact hc.intervalIntegrable

private noncomputable def circleCoord {ι : Type*} (x : ι → ℝ) (s r : ι) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0
    ((x r - x s : ℝ) : AddCircle (1 : ℝ))).1

private theorem circleCoord_mem {ι : Type*} (x : ι → ℝ) (s r : ι) :
    circleCoord x s r ∈ Ico (0 : ℝ) 1 := by
  simpa only [circleCoord, zero_add] using
    (AddCircle.equivIco (1 : ℝ) 0
      ((x r - x s : ℝ) : AddCircle (1 : ℝ))).2

private theorem circleCoord_coe {ι : Type*} (x : ι → ℝ) (s r : ι) :
    ((circleCoord x s r : ℝ) : AddCircle (1 : ℝ)) =
      ((x r - x s : ℝ) : AddCircle (1 : ℝ)) := by
  exact AddCircle.coe_equivIco

private theorem circleCoord_norm_le_left {ι : Type*} (x : ι → ℝ) (s r : ι) :
    ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖ ≤ circleCoord x s r := by
  rw [← circleCoord_coe x s r]
  calc
    ‖((circleCoord x s r : ℝ) : AddCircle (1 : ℝ))‖ ≤
        |circleCoord x s r| := QuotientAddGroup.norm_mk_le_norm
    _ = circleCoord x s r := abs_of_nonneg (circleCoord_mem x s r).1

private theorem circleCoord_norm_le_right {ι : Type*} (x : ι → ℝ) (s r : ι) :
    ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖ ≤ 1 - circleCoord x s r := by
  have hcoe :
      (((circleCoord x s r - 1 : ℝ) : AddCircle (1 : ℝ))) =
        ((x r - x s : ℝ) : AddCircle (1 : ℝ)) := by
    rw [AddCircle.coe_sub, circleCoord_coe]
    simp
  rw [← hcoe]
  calc
    ‖((circleCoord x s r - 1 : ℝ) : AddCircle (1 : ℝ))‖ ≤
        |circleCoord x s r - 1| := QuotientAddGroup.norm_mk_le_norm
    _ = 1 - circleCoord x s r := by
      rw [abs_of_nonpos]
      · ring
      · linarith [(circleCoord_mem x s r).2]

private theorem circleCoord_sub_coe {ι : Type*} (x : ι → ℝ) (s r t : ι) :
    (((circleCoord x s r - circleCoord x s t : ℝ) : AddCircle (1 : ℝ))) =
      ((x r - x t : ℝ) : AddCircle (1 : ℝ)) := by
  rw [AddCircle.coe_sub, circleCoord_coe, circleCoord_coe]
  rw [← AddCircle.coe_sub]
  congr 1
  ring

private theorem circleCoord_dist_ge {ι : Type*} (x : ι → ℝ) (s r t : ι) :
    ‖((x r - x t : ℝ) : AddCircle (1 : ℝ))‖ ≤
      |circleCoord x s r - circleCoord x s t| := by
  rw [← circleCoord_sub_coe x s r t]
  exact QuotientAddGroup.norm_mk_le_norm

private theorem sin_pi_circleCoord_sq {ι : Type*} (x : ι → ℝ) (s r : ι) :
    Real.sin (Real.pi * (x r - x s)) ^ 2 =
      Real.sin (Real.pi * circleCoord x s r) ^ 2 := by
  have hzero :
      (((x r - x s - circleCoord x s r : ℝ) : AddCircle (1 : ℝ))) = 0 := by
    rw [AddCircle.coe_sub, circleCoord_coe]
    simp
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  have hn' : (n : ℝ) = x r - x s - circleCoord x s r := by
    simpa using hn
  rw [show Real.pi * (x r - x s) =
    Real.pi * circleCoord x s r + (n : ℝ) * Real.pi by rw [hn']; ring,
    Real.sin_add_int_mul_pi]
  have hp : |((-1 : ℝ) ^ n)| = 1 := by
    rw [abs_zpow]
    norm_num
  have hp2 : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← sq_abs, hp]
    norm_num
  rw [mul_pow, hp2, one_mul]

private theorem sin_pi_circleCoord_sub_sq {ι : Type*} (x : ι → ℝ) (s r t : ι) :
    Real.sin (Real.pi * (x r - x t)) ^ 2 =
      Real.sin (Real.pi * (circleCoord x s r - circleCoord x s t)) ^ 2 := by
  have hzero :
      (((x r - x t - (circleCoord x s r - circleCoord x s t) : ℝ) :
          AddCircle (1 : ℝ))) = 0 := by
    rw [AddCircle.coe_sub, circleCoord_sub_coe]
    simp
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  have hn' : (n : ℝ) =
      x r - x t - (circleCoord x s r - circleCoord x s t) := by
    simpa using hn
  rw [show Real.pi * (x r - x t) =
    Real.pi * (circleCoord x s r - circleCoord x s t) + (n : ℝ) * Real.pi by
      rw [hn']; ring,
    Real.sin_add_int_mul_pi]
  have hp : |((-1 : ℝ) ^ n)| = 1 := by
    rw [abs_zpow]
    norm_num
  have hp2 : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← sq_abs, hp]
    norm_num
  rw [mul_pow, hp2, one_mul]

private theorem integral_cscSq_symmetric_le {d : ℝ} (hd : 0 < d) (hdhalf : d ≤ 1 / 2) :
    ∫ y in d / 2..1 - d / 2, cscSq y ≤ 4 / (Real.pi ^ 2 * d) := by
  have hA : 0 < d / 2 := by positivity
  have hAB : d / 2 ≤ 1 - d / 2 := by linarith
  have hB : 1 - d / 2 < 1 := by linarith
  rw [integral_cscSq hA hAB hB]
  simp only [cscSqAnti]
  rw [show Real.pi * (1 - d / 2) = Real.pi - Real.pi * (d / 2) by ring,
    Real.sin_pi_sub, Real.cos_pi_sub]
  let z : ℝ := Real.pi * (d / 2)
  have hz : 0 < z := by simp only [z]; positivity
  have hzhalf : z < Real.pi / 2 := by
    simp only [z]
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin z := Real.sin_pos_of_pos_of_lt_pi hz (hzhalf.trans (by linarith))
  have hcos : 0 < Real.cos z := by
    exact Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], hzhalf⟩
  have htan := Real.le_tan hz.le hzhalf
  rw [Real.tan_eq_sin_div_cos] at htan
  have hcot : Real.cos z / Real.sin z ≤ 1 / z := by
    rw [div_le_div_iff₀ hsin hz]
    simpa only [one_mul, mul_comm] using (le_div_iff₀ hcos).mp htan
  change -(-Real.cos z) / (Real.pi * Real.sin z) -
      (-Real.cos z / (Real.pi * Real.sin z)) ≤ _
  calc
    -(-Real.cos z) / (Real.pi * Real.sin z) -
        (-Real.cos z / (Real.pi * Real.sin z)) =
        2 / Real.pi * (Real.cos z / Real.sin z) := by
      field_simp [Real.pi_ne_zero, hsin.ne']
      ring
    _ ≤ 2 / Real.pi * (1 / z) := by
      gcongr
    _ = 4 / (Real.pi ^ 2 * d) := by
      simp only [z]
      field_simp [Real.pi_ne_zero, hd.ne']
      ring

private theorem circle_cscSq_sum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x δ : ι → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r t, r ≠ t →
      δ r ≤ ‖((x r - x t : ℝ) : AddCircle (1 : ℝ))‖) (s : ι) :
    ∑ r ∈ Finset.univ.erase s, δ r * cscSq (circleCoord x s r) ≤
      4 / (Real.pi ^ 2 * δ s) := by
  classical
  by_cases hne : (Finset.univ.erase s).Nonempty
  · obtain ⟨r, hr⟩ := hne
    have hrs : r ≠ s := (Finset.mem_erase.mp hr).1
    have hssep := hsep s r (Ne.symm hrs)
    have hhalf :
        ‖((x s - x r : ℝ) : AddCircle (1 : ℝ))‖ ≤ 1 / 2 := by
      simpa only [abs_one, one_div] using
        (AddCircle.norm_le_half_period (1 : ℝ)
          (x := ((x s - x r : ℝ) : AddCircle (1 : ℝ))) (by norm_num))
    have hdhalf : δ s ≤ 1 / 2 := hssep.trans hhalf
    let c : {r : ι // r ≠ s} → ℝ := fun r => circleCoord x s r
    let w : {r : ι // r ≠ s} → ℝ := fun r => δ r
    have hds : 0 < δ s := hδ s
    have hApos : 0 < δ s / 2 := by linarith
    have hBlt : 1 - δ s / 2 < 1 := by linarith
    have hAB : δ s / 2 ≤ 1 - δ s / 2 := by linarith
    have hleft (a : {r : ι // r ≠ s}) :
        δ s / 2 ≤ c a - w a / 2 := by
      have har := hsep a s a.property
      have hsa0 := hsep s a (Ne.symm a.property)
      have hsa : δ s ≤
          ‖((x a - x s : ℝ) : AddCircle (1 : ℝ))‖ := by
        simpa only [AddCircle.coe_sub] using hsa0.trans_eq
          (norm_sub_rev ((x s : ℝ) : AddCircle (1 : ℝ))
            ((x a : ℝ) : AddCircle (1 : ℝ)))
      have hcoord := circleCoord_norm_le_left x s a
      dsimp only [c, w]
      linarith
    have hright (a : {r : ι // r ≠ s}) :
        c a + w a / 2 ≤ 1 - δ s / 2 := by
      have har := hsep a s a.property
      have hsa0 := hsep s a (Ne.symm a.property)
      have hsa : δ s ≤
          ‖((x a - x s : ℝ) : AddCircle (1 : ℝ))‖ := by
        simpa only [AddCircle.coe_sub] using hsa0.trans_eq
          (norm_sub_rev ((x s : ℝ) : AddCircle (1 : ℝ))
            ((x a : ℝ) : AddCircle (1 : ℝ)))
      have hcoord := circleCoord_norm_le_right x s a
      dsimp only [c, w]
      linarith
    have hpsep (a b : {r : ι // r ≠ s}) (hab : a ≠ b) :
        (w a + w b) / 2 ≤ |c a - c b| := by
      have habv : (a : ι) ≠ b := by
        intro h
        exact hab (Subtype.ext h)
      have hab0 := hsep a b habv
      have hba0 := hsep b a (Ne.symm habv)
      have hba : δ b ≤
          ‖((x a - x b : ℝ) : AddCircle (1 : ℝ))‖ := by
        simpa only [AddCircle.coe_sub] using hba0.trans_eq
          (norm_sub_rev ((x b : ℝ) : AddCircle (1 : ℝ))
            ((x a : ℝ) : AddCircle (1 : ℝ)))
      have hcoord := circleCoord_dist_ge x s a b
      dsimp only [c, w]
      linarith
    have hpack := convex_packed_sum_le_integral cscSq c w hAB
      (fun a => hδ a) hleft hright hpsep
      (cscSq_convexOn hApos hBlt)
      (cscSq_continuousOn hApos hBlt)
      (by
        intro y hy
        simp only [cscSq]
        positivity)
    have hsum :
        (∑ r ∈ Finset.univ.erase s, δ r * cscSq (circleCoord x s r)) =
          ∑ a : {r : ι // r ≠ s}, w a * cscSq (c a) := by
      rw [Finset.sum_subtype (p := fun r => r ≠ s) (Finset.univ.erase s)
        (by intro a; simp)
        (fun r => δ r * cscSq (circleCoord x s r))]
    rw [hsum]
    exact hpack.trans (integral_cscSq_symmetric_le (hδ s) hdhalf)
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp only [Finset.sum_empty]
    have hds : 0 < δ s := hδ s
    positivity

private theorem circle_cscSqProduct_sum_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] (x δ : ι → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r t, r ≠ t →
      δ r ≤ ‖((x r - x t : ℝ) : AddCircle (1 : ℝ))‖)
    (s t : ι) (hst : s ≠ t) :
    ∑ r ∈ (Finset.univ.erase s).erase t,
        δ r * cscSqProduct (circleCoord x s t) (circleCoord x s r) ≤
      4 / Real.pi ^ 2 * (1 / δ s + 1 / δ t) * cscSq (circleCoord x s t) := by
  classical
  let a : ℝ := circleCoord x s t
  let U : Finset ι := (Finset.univ.erase s).erase t
  have hds : 0 < δ s := hδ s
  have hdt : 0 < δ t := hδ t
  have hts0 := hsep t s (Ne.symm hst)
  have hst0 := hsep s t hst
  have hst' : δ s ≤ ‖((x t - x s : ℝ) : AddCircle (1 : ℝ))‖ := by
    simpa only [AddCircle.coe_sub] using hst0.trans_eq
      (norm_sub_rev ((x s : ℝ) : AddCircle (1 : ℝ))
        ((x t : ℝ) : AddCircle (1 : ℝ)))
  have haLeft : (δ s + δ t) / 2 ≤ a := by
    have hc := circleCoord_norm_le_left x s t
    dsimp only [a]
    linarith
  have haRight : (δ s + δ t) / 2 ≤ 1 - a := by
    have hc := circleCoord_norm_le_right x s t
    dsimp only [a]
    linarith
  have ha0 : 0 < a := by linarith [hδ s, hδ t]
  have ha1 : a < 1 := by linarith [hδ s, hδ t]
  have hmemU (r : ι) (hr : r ∈ U) : r ≠ s ∧ r ≠ t := by
    dsimp only [U] at hr
    exact ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1,
      (Finset.mem_erase.mp hr).1⟩
  have hcoordNe (r : ι) (hr : r ∈ U) : circleCoord x s r ≠ a := by
    intro hre
    have hrt := (hmemU r hr).2
    have hsepRT := hsep r t hrt
    have hc := circleCoord_dist_ge x s r t
    dsimp only [a] at hre
    rw [hre, sub_self, abs_zero] at hc
    linarith [hδ r]
  have houterLeft (r : ι) (hrs : r ≠ s) :
      δ s / 2 ≤ circleCoord x s r - δ r / 2 := by
    have hrs0 := hsep r s hrs
    have hsr0 := hsep s r (Ne.symm hrs)
    have hsr : δ s ≤ ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖ := by
      simpa only [AddCircle.coe_sub] using hsr0.trans_eq
        (norm_sub_rev ((x s : ℝ) : AddCircle (1 : ℝ))
          ((x r : ℝ) : AddCircle (1 : ℝ)))
    have hc := circleCoord_norm_le_left x s r
    linarith
  have houterRight (r : ι) (hrs : r ≠ s) :
      circleCoord x s r + δ r / 2 ≤ 1 - δ s / 2 := by
    have hrs0 := hsep r s hrs
    have hsr0 := hsep s r (Ne.symm hrs)
    have hsr : δ s ≤ ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖ := by
      simpa only [AddCircle.coe_sub] using hsr0.trans_eq
        (norm_sub_rev ((x s : ℝ) : AddCircle (1 : ℝ))
          ((x r : ℝ) : AddCircle (1 : ℝ)))
    have hc := circleCoord_norm_le_right x s r
    linarith
  have htLeft (r : ι) (hrt : r ≠ t) (hrpos : circleCoord x s r < a) :
      circleCoord x s r + δ r / 2 ≤ a - δ t / 2 := by
    have hrt0 := hsep r t hrt
    have htr0 := hsep t r (Ne.symm hrt)
    have htr : δ t ≤ ‖((x r - x t : ℝ) : AddCircle (1 : ℝ))‖ := by
      simpa only [AddCircle.coe_sub] using htr0.trans_eq
        (norm_sub_rev ((x t : ℝ) : AddCircle (1 : ℝ))
          ((x r : ℝ) : AddCircle (1 : ℝ)))
    have hc := circleCoord_dist_ge x s r t
    dsimp only [a] at hrpos ⊢
    rw [abs_of_nonpos (sub_nonpos.mpr hrpos.le)] at hc
    linarith
  have htRight (r : ι) (hrt : r ≠ t) (hrpos : a < circleCoord x s r) :
      a + δ t / 2 ≤ circleCoord x s r - δ r / 2 := by
    have hrt0 := hsep r t hrt
    have htr0 := hsep t r (Ne.symm hrt)
    have htr : δ t ≤ ‖((x r - x t : ℝ) : AddCircle (1 : ℝ))‖ := by
      simpa only [AddCircle.coe_sub] using htr0.trans_eq
        (norm_sub_rev ((x t : ℝ) : AddCircle (1 : ℝ))
          ((x r : ℝ) : AddCircle (1 : ℝ)))
    have hc := circleCoord_dist_ge x s r t
    dsimp only [a] at hrpos ⊢
    rw [abs_of_nonneg (sub_nonneg.mpr hrpos.le)] at hc
    linarith
  have hpsep (r u : ι) (hru : r ≠ u) :
      (δ r + δ u) / 2 ≤ |circleCoord x s r - circleCoord x s u| := by
    have hru0 := hsep r u hru
    have hur0 := hsep u r (Ne.symm hru)
    have hur : δ u ≤ ‖((x r - x u : ℝ) : AddCircle (1 : ℝ))‖ := by
      simpa only [AddCircle.coe_sub] using hur0.trans_eq
        (norm_sub_rev ((x u : ℝ) : AddCircle (1 : ℝ))
          ((x r : ℝ) : AddCircle (1 : ℝ)))
    have hc := circleCoord_dist_ge x s r u
    linarith
  have hAB₁ : δ s / 2 ≤ a - δ t / 2 := by linarith
  have hAB₂ : a + δ t / 2 ≤ 1 - δ s / 2 := by linarith
  have hy₁ (y : ℝ) (hy : y ∈ Icc (δ s / 2) (a - δ t / 2)) :
      Real.sin (Real.pi * y) ≠ 0 := by
    exact (sin_pi_mul_pos (by linarith [hy.1, hds])
      (by linarith [hy.2, hdt, ha1])).ne'
  have hya₁ (y : ℝ) (hy : y ∈ Icc (δ s / 2) (a - δ t / 2)) :
      Real.sin (Real.pi * (y - a)) ≠ 0 := by
    have hsine := sin_pi_mul_pos (by linarith [hy.2, hdt] : 0 < a - y)
      (by linarith [hy.1, hds, ha1] : a - y < 1)
    rw [show Real.pi * (y - a) = -(Real.pi * (a - y)) by ring, Real.sin_neg]
    exact neg_ne_zero.mpr hsine.ne'
  have hy₂ (y : ℝ) (hy : y ∈ Icc (a + δ t / 2) (1 - δ s / 2)) :
      Real.sin (Real.pi * y) ≠ 0 := by
    exact (sin_pi_mul_pos (by linarith [hy.1, hdt, ha0])
      (by linarith [hy.2, hds])).ne'
  have hya₂ (y : ℝ) (hy : y ∈ Icc (a + δ t / 2) (1 - δ s / 2)) :
      Real.sin (Real.pi * (y - a)) ≠ 0 := by
    exact (sin_pi_mul_pos (by linarith [hy.1, hdt])
      (by linarith [hy.2, hds, ha0])).ne'
  let PL : ι → Prop := fun r => r ∈ U ∧ circleCoord x s r < a
  let PR : ι → Prop := fun r => r ∈ U ∧ ¬circleCoord x s r < a
  let cL : Subtype PL → ℝ := fun r => circleCoord x s r
  let cR : Subtype PR → ℝ := fun r => circleCoord x s r
  let wL : Subtype PL → ℝ := fun r => δ r
  let wR : Subtype PR → ℝ := fun r => δ r
  have hpackL := convex_packed_sum_le_integral (cscSqProduct a) cL wL hAB₁
    (fun r => hδ r)
    (fun r => by
      dsimp only [cL, wL]
      exact houterLeft r (hmemU r r.property.1).1)
    (fun r => by
      dsimp only [cL, wL]
      exact htLeft r (hmemU r r.property.1).2 r.property.2)
    (fun r u hru => by
      have hruv : (r : ι) ≠ u := by
        intro h
        exact hru (Subtype.ext h)
      simpa only [cL, wL] using hpsep r u hruv)
    (cscSqProduct_convexOn hy₁ hya₁)
    (cscSqProduct_continuousOn hy₁ hya₁)
    (by intro y hy; simp only [cscSqProduct, cscSq]; positivity)
  have hpackR := convex_packed_sum_le_integral (cscSqProduct a) cR wR hAB₂
    (fun r => hδ r)
    (fun r => by
      dsimp only [cR, wR]
      have hrt := (hmemU r r.property.1).2
      have hne := hcoordNe r r.property.1
      exact htRight r hrt (lt_of_le_of_ne (le_of_not_gt r.property.2) (Ne.symm hne)))
    (fun r => by
      dsimp only [cR, wR]
      exact houterRight r (hmemU r r.property.1).1)
    (fun r u hru => by
      have hruv : (r : ι) ≠ u := by
        intro h
        exact hru (Subtype.ext h)
      simpa only [cR, wR] using hpsep r u hruv)
    (cscSqProduct_convexOn hy₂ hya₂)
    (cscSqProduct_continuousOn hy₂ hya₂)
    (by intro y hy; simp only [cscSqProduct, cscSq]; positivity)
  have hsumL :
      (∑ r ∈ U.filter fun r => circleCoord x s r < a,
          δ r * cscSqProduct a (circleCoord x s r)) =
        ∑ r : Subtype PL, wL r * cscSqProduct a (cL r) := by
    rw [Finset.sum_subtype (p := PL) (U.filter fun r => circleCoord x s r < a)
      (by intro r; simp [PL])
      (fun r => δ r * cscSqProduct a (circleCoord x s r))]
  have hsumR :
      (∑ r ∈ U.filter fun r => ¬circleCoord x s r < a,
          δ r * cscSqProduct a (circleCoord x s r)) =
        ∑ r : Subtype PR, wR r * cscSqProduct a (cR r) := by
    rw [Finset.sum_subtype (p := PR) (U.filter fun r => ¬circleCoord x s r < a)
      (by intro r; simp [PR])
      (fun r => δ r * cscSqProduct a (circleCoord x s r))]
  change (∑ r ∈ U, δ r * cscSqProduct a (circleCoord x s r)) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not U
    (fun r => circleCoord x s r < a), hsumL, hsumR]
  calc
    (∑ r : Subtype PL, wL r * cscSqProduct a (cL r)) +
        ∑ r : Subtype PR, wR r * cscSqProduct a (cR r) ≤
      (∫ y in δ s / 2..a - δ t / 2, cscSqProduct a y) +
        ∫ y in a + δ t / 2..1 - δ s / 2, cscSqProduct a y :=
      add_le_add hpackL hpackR
    _ ≤ 4 / Real.pi ^ 2 * (1 / δ s + 1 / δ t) * cscSq a :=
      integral_cscSqProduct_two_arcs_le (hδ s) (hδ t) haLeft haRight
    _ = 4 / Real.pi ^ 2 * (1 / δ s + 1 / δ t) *
        cscSq (circleCoord x s t) := by rfl

open scoped ComplexConjugate Matrix.Norms.L2Operator

open Matrix

private noncomputable def weightedMatrix {ι : Type*} (δ : ι → ℝ)
    (K : ι → ι → ℝ) : Matrix ι ι ℂ :=
  fun r s ↦ Complex.I * Real.sqrt (δ r) * Real.sqrt (δ s) * K r s

private theorem weightedMatrix_isHermitian {ι : Type*} (δ : ι → ℝ)
    (K : ι → ι → ℝ)
    (hK : ∀ r s, K s r = -K r s) :
    (weightedMatrix δ K).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro r s
  change (starRingEnd ℂ)
      (Complex.I * Real.sqrt (δ s) * Real.sqrt (δ r) * K s r) = _
  rw [hK r s]
  simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal,
    Complex.ofReal_neg]
  unfold weightedMatrix
  ring

private theorem hermitian_norm_le_of_eigenvalues_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (C : ℝ) (hC : ∀ i, |hA.eigenvalues i| ≤ C) : ‖A‖ ≤ C := by
  rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  let U : Matrix.unitaryGroup ι ℂ := hA.eigenvectorUnitary
  let D : Matrix ι ι ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hUD : ‖(U : Matrix ι ι ℂ) * D * star (U : Matrix ι ι ℂ)‖ ≤ ‖D‖ := by
    calc
      ‖(U : Matrix ι ι ℂ) * D * star (U : Matrix ι ι ℂ)‖ ≤
          ‖(U : Matrix ι ι ℂ) * D‖ * ‖star (U : Matrix ι ι ℂ)‖ :=
        Matrix.l2_opNorm_mul _ _
      _ ≤ (‖(U : Matrix ι ι ℂ)‖ * ‖D‖) * ‖star (U : Matrix ι ι ℂ)‖ := by
        gcongr
        exact Matrix.l2_opNorm_mul _ _
      _ = ‖D‖ := by
        rw [CStarRing.norm_coe_unitary U]
        simp
  refine hUD.trans ?_
  dsimp only [D]
  rw [Matrix.l2_opNorm_diagonal]
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  have hC0 : 0 ≤ C := (abs_nonneg (hA.eigenvalues i₀)).trans (hC i₀)
  rw [pi_norm_le_iff_of_nonneg hC0]
  intro i
  simpa using hC i

private theorem bilinear_le_of_weightedMatrix_norm {ι : Type*} [Fintype ι]
    [DecidableEq ι] (δ : ι → ℝ) (K : ι → ι → ℝ) (C : ℝ)
    (hδ : ∀ r, 0 < δ r) (z : ι → ℂ)
    (hA : ‖weightedMatrix δ K‖ ≤ C) :
    ‖∑ r, ∑ s, z r * conj (z s) * K r s‖ ≤
      C * ∑ r, ‖z r‖ ^ 2 / δ r := by
  let w : EuclideanSpace ℂ ι :=
    WithLp.toLp 2 (fun r ↦ conj (z r) / Real.sqrt (δ r))
  have hw_sq : ‖w‖ ^ 2 = ∑ r, ‖z r‖ ^ 2 / δ r := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro r _
    simp only [w, norm_div, Complex.norm_real, Real.norm_eq_abs, div_pow]
    rw [RCLike.norm_conj, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (hδ r).le]
  have hinner :
      inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) (weightedMatrix δ K) w) =
        Complex.I * ∑ r, ∑ s, z r * conj (z s) * K r s := by
    rw [PiLp.inner_apply]
    simp only [Matrix.ofLp_toEuclideanCLM]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [RCLike.inner_apply]
    simp only [Matrix.mulVec, w, weightedMatrix, dotProduct, map_div₀,
      Complex.conj_ofReal]
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    have hr : (Real.sqrt (δ r) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (hδ r)).ne'
    have hs : (Real.sqrt (δ s) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (hδ s)).ne'
    field_simp
    rw [RCLike.conj_conj]
  rw [← hw_sq]
  calc
    ‖∑ r, ∑ s, z r * conj (z s) * K r s‖ =
        ‖inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) (weightedMatrix δ K) w)‖ := by
      rw [hinner]
      simp
    _ ≤ ‖w‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (weightedMatrix δ K) w‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖w‖ *
        (‖Matrix.toEuclideanCLM (𝕜 := ℂ) (weightedMatrix δ K)‖ * ‖w‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖weightedMatrix δ K‖ * ‖w‖ ^ 2 := by
      rw [Matrix.l2_opNorm_toEuclideanCLM]
      ring
    _ ≤ C * ‖w‖ ^ 2 := by gcongr

private theorem weightedKernel_norm_sum_expand {ι : Type*} [Fintype ι]
    (δ : ι → ℝ) (K : ι → ι → ℝ) (u : ι → ℂ) :
    ((∑ r, δ r * ‖∑ s, (K r s : ℂ) * u s‖ ^ 2 : ℝ) : ℂ) =
      ∑ r, ∑ t, ∑ s, (δ r * (K r s * K r t) : ℝ) * u s * conj (u t) := by
  push_cast
  apply Finset.sum_congr rfl
  intro r _
  rw [← Complex.mul_conj']
  simp only [map_sum, map_mul, Complex.conj_ofReal]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem weightedKernel_main_terms_cancel {ι : Type*} [Fintype ι]
    (δ : ι → ℝ) (K L : ι → ι → ℝ) (u : ι → ℂ) (μ : ℝ)
    (hK : ∀ r s, K s r = -K r s)
    (heig : ∀ r, ∑ s, (K r s : ℂ) * u s =
      -Complex.I * μ * u r / δ r) :
    (∑ r, ∑ s, ∑ t,
        (δ r * K s t * L r s : ℝ) * u s * conj (u t)) =
      ∑ r, ∑ s, ∑ t,
        (δ r * K s t * L r t : ℝ) * u s * conj (u t) := by
  have heigConj (s : ι) :
      ∑ t, (K s t : ℂ) * conj (u t) =
        Complex.I * μ * conj (u s) / δ s := by
    have h := congrArg (starRingEnd ℂ) (heig s)
    simp only [map_sum, map_mul, Complex.conj_ofReal, map_div₀, map_neg,
      Complex.conj_I] at h
    convert h using 1
    all_goals ring
  have heigReverse (t : ι) :
      ∑ s, (K s t : ℂ) * u s = Complex.I * μ * u t / δ t := by
    calc
      ∑ s, (K s t : ℂ) * u s = -∑ s, (K t s : ℂ) * u s := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro s _
        rw [hK t s]
        push_cast
        ring
      _ = Complex.I * μ * u t / δ t := by rw [heig]; ring
  calc
    (∑ r, ∑ s, ∑ t,
        (δ r * K s t * L r s : ℝ) * u s * conj (u t)) =
        ∑ r, ∑ s, (δ r * L r s : ℂ) * u s *
          (Complex.I * μ * conj (u s) / δ s) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      rw [← heigConj s, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      push_cast
      ring
    _ = ∑ r, ∑ t, (δ r * L r t : ℂ) *
          (Complex.I * μ * u t / δ t) * conj (u t) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = ∑ r, ∑ t, ∑ s,
        (δ r * K s t * L r t : ℝ) * u s * conj (u t) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro t _
      rw [← heigReverse t, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      push_cast
      ring
    _ = ∑ r, ∑ s, ∑ t,
        (δ r * K s t * L r t : ℝ) * u s * conj (u t) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]

private theorem weightedKernel_triple_reduce {ι : Type*} [Fintype ι]
    [DecidableEq ι] (δ : ι → ℝ) (K L : ι → ι → ℝ) (u : ι → ℂ) (μ : ℝ)
    (hK : ∀ r s, K s r = -K r s)
    (hKL : ∀ r s t,
      K r s * K r t = K s t * (L r s - L r t) +
        (if r = s then K s t * L s t else 0) +
        (if r = t then K s t * L s t else 0) +
        (if s = t then K r s ^ 2 else 0))
    (heig : ∀ r, ∑ s, (K r s : ℂ) * u s =
      -Complex.I * μ * u r / δ r) :
    (∑ r, ∑ s, ∑ t,
        (δ r * (K r s * K r t) : ℝ) * u s * conj (u t)) =
      (∑ s, ∑ r, δ r * K r s ^ 2 * ‖u s‖ ^ 2 : ℝ) +
        ∑ s, ∑ t,
          ((δ s + δ t) * K s t * L s t : ℝ) * u s * conj (u t) := by
  have hcancel := weightedKernel_main_terms_cancel δ K L u μ hK heig
  have hmain :
      (∑ r, ∑ s, ∑ t,
          (δ r * (K s t * (L r s - L r t)) : ℝ) * u s * conj (u t)) = 0 := by
    rw [show (0 : ℂ) =
      (∑ r, ∑ s, ∑ t,
          (δ r * K s t * L r s : ℝ) * u s * conj (u t)) -
        ∑ r, ∑ s, ∑ t,
          (δ r * K s t * L r t : ℝ) * u s * conj (u t) by rw [hcancel, sub_self]]
    simp_rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    push_cast
    ring
  have hpoint (r s t : ι) :
      (δ r * (K r s * K r t) : ℝ) * u s * conj (u t) =
        (δ r * (K s t * (L r s - L r t)) : ℝ) * u s * conj (u t) +
        (if r = s then (δ r * K s t * L s t : ℝ) * u s * conj (u t) else 0) +
        (if r = t then (δ r * K s t * L s t : ℝ) * u s * conj (u t) else 0) +
        (if s = t then (δ r * K r s ^ 2 : ℝ) * u s * conj (u t) else 0) := by
    rw [hKL]
    split_ifs <;> push_cast <;> ring
  have hswap :
      (∑ r, ∑ s,
          (δ r : ℂ) * K s r * L s r * u s * conj (u r)) =
        ∑ s, ∑ t,
          (δ t : ℂ) * K s t * L s t * u s * conj (u t) := by
    rw [Finset.sum_comm]
  have hdiag :
      (∑ r, ∑ s, (δ r : ℂ) * (K r s : ℂ) ^ 2 * u s * conj (u s)) =
        ∑ s, ∑ r, (δ r : ℂ) * (K r s : ℂ) ^ 2 * (‖u s‖ : ℂ) ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro r _
    rw [← Complex.mul_conj']
    ring
  have hcorr :
      (∑ s, ∑ t, ((δ s : ℂ) + δ t) * K s t * L s t * u s * conj (u t)) =
        (∑ s, ∑ t, (δ s : ℂ) * K s t * L s t * u s * conj (u t)) +
          ∑ s, ∑ t, (δ t : ℂ) * K s t * L s t * u s * conj (u t) := by
    simp_rw [add_mul, Finset.sum_add_distrib]
  simp_rw [hpoint, Finset.sum_add_distrib, hmain, zero_add]
  simp only [Complex.ofReal_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Complex.ofReal_pow,
    Complex.ofReal_sum, Complex.ofReal_add]
  rw [hswap, hdiag, hcorr]
  ring

private theorem weightedKernel_eigenvalue_sq_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] (δ : ι → ℝ) (K L : ι → ι → ℝ) (u : ι → ℂ) (μ : ℝ)
    (hδ : ∀ r, 0 < δ r)
    (hK : ∀ r s, K s r = -K r s)
    (hKL : ∀ r s t,
      K r s * K r t = K s t * (L r s - L r t) +
        (if r = s then K s t * L s t else 0) +
        (if r = t then K s t * L s t else 0) +
        (if s = t then K r s ^ 2 else 0))
    (hLK : ∀ r s, |L r s| ≤ |K r s|)
    (hA : ∀ s, ∑ r, δ r * K r s ^ 2 ≤ (811 / 2000 : ℝ) / δ s)
    (hB : ∀ s, ∑ r, δ r * K r s ^ 4 ≤ (203 / 2000 : ℝ) / δ s ^ 3)
    (hC : ∀ s t, s ≠ t →
      ∑ r, δ r * K r s ^ 2 * K r t ^ 2 ≤
        (811 / 2000 : ℝ) * (1 / δ s + 1 / δ t) * K s t ^ 2)
    (hnorm : ∑ r, ‖u r‖ ^ 2 / δ r = 1)
    (heig : ∀ r, ∑ s, (K r s : ℂ) * u s =
      -Complex.I * μ * u r / δ r) :
    μ ^ 2 ≤ 9 / 4 := by
  have hδne : ∀ r, δ r ≠ 0 := fun r ↦ (hδ r).ne'
  have hμ : μ ^ 2 =
      ∑ r, δ r * ‖∑ s, (K r s : ℂ) * u s‖ ^ 2 := by
    calc
      μ ^ 2 = μ ^ 2 * (∑ r, ‖u r‖ ^ 2 / δ r) := by rw [hnorm, mul_one]
      _ = ∑ r, δ r * ‖-Complex.I * μ * u r / δ r‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        rw [norm_div, norm_mul, norm_mul]
        simp only [norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (hδ r)]
        field_simp
        rw [sq_abs]
        ring
      _ = ∑ r, δ r * ‖∑ s, (K r s : ℂ) * u s‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro r _
        rw [heig]
  let T₁ : ℝ := ∑ s, ∑ r, δ r * K r s ^ 2 * ‖u s‖ ^ 2
  let T₂ : ℂ := ∑ s, ∑ t,
    ((δ s + δ t) * K s t * L s t : ℝ) * u s * conj (u t)
  let T₆ : ℝ := ∑ s, ∑ t,
    (δ s + δ t) * K s t ^ 2 * ‖u s‖ * ‖u t‖
  have hdecomp : μ ^ 2 = T₁ + T₂.re := by
    have hc : ((μ ^ 2 : ℝ) : ℂ) = (T₁ : ℂ) + T₂ := by
      calc
        ((μ ^ 2 : ℝ) : ℂ) =
            ((∑ r, δ r * ‖∑ s, (K r s : ℂ) * u s‖ ^ 2 : ℝ) : ℂ) := by
          rw [hμ]
        _ = ∑ r, ∑ t, ∑ s,
            (δ r * (K r s * K r t) : ℝ) * u s * conj (u t) :=
          weightedKernel_norm_sum_expand δ K u
        _ = ∑ r, ∑ s, ∑ t,
            (δ r * (K r s * K r t) : ℝ) * u s * conj (u t) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [Finset.sum_comm]
        _ = (T₁ : ℂ) + T₂ := by
          simpa only [T₁, T₂] using
            weightedKernel_triple_reduce δ K L u μ hK hKL heig
    have hr := congrArg Complex.re hc
    simpa only [Complex.add_re, Complex.ofReal_re] using hr
  have hT₁ : T₁ ≤ 811 / 2000 := by
    calc
      T₁ = ∑ s, ‖u s‖ ^ 2 * ∑ r, δ r * K r s ^ 2 := by
        simp only [T₁]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring
      _ ≤ ∑ s, ‖u s‖ ^ 2 * ((811 / 2000 : ℝ) / δ s) := by
        gcongr with s
        exact hA s
      _ = 811 / 2000 := by
        calc
          (∑ s, ‖u s‖ ^ 2 * ((811 / 2000 : ℝ) / δ s)) =
              (811 / 2000 : ℝ) * ∑ s, ‖u s‖ ^ 2 / δ s := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s _
            ring
          _ = 811 / 2000 := by rw [hnorm, mul_one]
  have hT₂ : T₂.re ≤ T₆ := by
    calc
      T₂.re ≤ ‖T₂‖ := Complex.re_le_norm _
      _ ≤ ∑ s, ∑ t, ‖((δ s + δ t) * K s t * L s t : ℝ) *
          u s * conj (u t)‖ := by
        simp only [T₂]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ ↦ norm_sum_le _ _)
      _ ≤ T₆ := by
        simp only [T₆]
        gcongr with s t
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          RCLike.norm_conj]
        rw [abs_of_pos (add_pos (hδ s) (hδ t)), ← sq_abs (K s t)]
        have hc : 0 ≤ (δ s + δ t) * |K s t| :=
          mul_nonneg (add_pos (hδ s) (hδ t)).le (abs_nonneg _)
        have h := mul_le_mul_of_nonneg_left (hLK s t) hc
        have h' := mul_le_mul_of_nonneg_right h (norm_nonneg (u s))
        have h'' := mul_le_mul_of_nonneg_right h' (norm_nonneg (u t))
        simpa only [mul_assoc, pow_two] using h''
  have hKsq (s t : ι) : K s t ^ 2 = K t s ^ 2 := by
    rw [hK s t]
    ring
  let P : ℝ := ∑ t, ‖u t‖ * ∑ s, δ s * ‖u s‖ * K s t ^ 2
  let Q : ℝ := ∑ t, δ t * (∑ s, δ s * ‖u s‖ * K s t ^ 2) ^ 2
  have hT₆P : T₆ = 2 * P := by
    calc
      T₆ = (∑ s, ∑ t, δ s * K s t ^ 2 * ‖u s‖ * ‖u t‖) +
          ∑ s, ∑ t, δ t * K s t ^ 2 * ‖u s‖ * ‖u t‖ := by
        simp only [T₆]
        rw [show (∑ s, ∑ t, (δ s + δ t) * K s t ^ 2 * ‖u s‖ * ‖u t‖) =
          ∑ s, ∑ t, (δ s * K s t ^ 2 * ‖u s‖ * ‖u t‖ +
            δ t * K s t ^ 2 * ‖u s‖ * ‖u t‖) by
              apply Finset.sum_congr rfl
              intro s _
              apply Finset.sum_congr rfl
              intro t _
              ring]
        simp only [Finset.sum_add_distrib]
      _ = 2 * ∑ s, ∑ t, δ s * K s t ^ 2 * ‖u s‖ * ‖u t‖ := by
        rw [show (∑ s, ∑ t, δ t * K s t ^ 2 * ‖u s‖ * ‖u t‖) =
          ∑ s, ∑ t, δ s * K s t ^ 2 * ‖u s‖ * ‖u t‖ by
            calc
              (∑ s, ∑ t, δ t * K s t ^ 2 * ‖u s‖ * ‖u t‖) =
                  ∑ s, ∑ t, δ s * K t s ^ 2 * ‖u t‖ * ‖u s‖ := by
                rw [Finset.sum_comm]
              _ = ∑ s, ∑ t, δ s * K s t ^ 2 * ‖u s‖ * ‖u t‖ := by
                apply Finset.sum_congr rfl
                intro s _
                apply Finset.sum_congr rfl
                intro t _
                rw [← hKsq s t]
                ring]
        ring
      _ = 2 * P := by
        congr 1
        simp only [P]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        ring
  have hF : ∑ t, (‖u t‖ / Real.sqrt (δ t)) ^ 2 = 1 := by
    rw [← hnorm]
    apply Finset.sum_congr rfl
    intro t _
    rw [div_pow, Real.sq_sqrt (hδ t).le]
  have hG :
      ∑ t, (Real.sqrt (δ t) * ∑ s, δ s * ‖u s‖ * K s t ^ 2) ^ 2 = Q := by
    simp only [Q]
    apply Finset.sum_congr rfl
    intro t _
    rw [mul_pow, Real.sq_sqrt (hδ t).le]
  have hPfg : P = ∑ t, (‖u t‖ / Real.sqrt (δ t)) *
      (Real.sqrt (δ t) * ∑ s, δ s * ‖u s‖ * K s t ^ 2) := by
    simp only [P]
    apply Finset.sum_congr rfl
    intro t _
    have ht : Real.sqrt (δ t) ≠ 0 := (Real.sqrt_pos.2 (hδ t)).ne'
    field_simp
  have hP2 : P ^ 2 ≤ Q := by
    rw [hPfg]
    calc
      (∑ t, (‖u t‖ / Real.sqrt (δ t)) *
          (Real.sqrt (δ t) * ∑ s, δ s * ‖u s‖ * K s t ^ 2)) ^ 2 ≤
          (∑ t, (‖u t‖ / Real.sqrt (δ t)) ^ 2) *
            ∑ t, (Real.sqrt (δ t) * ∑ s, δ s * ‖u s‖ * K s t ^ 2) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
      _ = Q := by rw [hF, hG, one_mul]
  have hKdiag (s : ι) : K s s = 0 := by
    have hs := hK s s
    linarith
  have hQexpand : Q = ∑ s, ∑ l,
      δ s * δ l * ‖u s‖ * ‖u l‖ *
        ∑ t, δ t * K s t ^ 2 * K l t ^ 2 := by
    calc
      Q = ∑ t, ∑ s, ∑ l,
          δ t * (δ s * ‖u s‖ * K s t ^ 2) *
            (δ l * ‖u l‖ * K l t ^ 2) := by
        simp only [Q]
        apply Finset.sum_congr rfl
        intro t _
        rw [pow_two, Finset.sum_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = ∑ s, ∑ l, ∑ t,
          δ t * (δ s * ‖u s‖ * K s t ^ 2) *
            (δ l * ‖u l‖ * K l t ^ 2) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.sum_comm]
      _ = ∑ s, ∑ l,
          δ s * δ l * ‖u s‖ * ‖u l‖ *
            ∑ t, δ t * K s t ^ 2 * K l t ^ 2 := by
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro l _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        ring
  have hInner (s l : ι) :
      (∑ t, δ t * K s t ^ 2 * K l t ^ 2) ≤
        (if s = l then (203 / 2000 : ℝ) / δ s ^ 3 else 0) +
          (811 / 2000 : ℝ) * (1 / δ s + 1 / δ l) * K s l ^ 2 := by
    by_cases hsl : s = l
    · subst l
      simp only [ite_true, hKdiag, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, add_zero]
      rw [show (∑ t, δ t * K s t ^ 2 * K s t ^ 2) =
        ∑ t, δ t * K t s ^ 4 by
          apply Finset.sum_congr rfl
          intro t _
          rw [hKsq s t]
          ring]
      exact hB s
    · simp only [hsl, ite_false, zero_add]
      rw [show (∑ t, δ t * K s t ^ 2 * K l t ^ 2) =
        ∑ t, δ t * K t s ^ 2 * K t l ^ 2 by
          apply Finset.sum_congr rfl
          intro t _
          rw [hKsq s t, hKsq l t]]
      exact hC s l hsl
  have hQraw : Q ≤ ∑ s, ∑ l,
      δ s * δ l * ‖u s‖ * ‖u l‖ *
        ((if s = l then (203 / 2000 : ℝ) / δ s ^ 3 else 0) +
          (811 / 2000 : ℝ) * (1 / δ s + 1 / δ l) * K s l ^ 2) := by
    rw [hQexpand]
    apply Finset.sum_le_sum
    intro s _
    apply Finset.sum_le_sum
    intro l _
    have hcoef : 0 ≤ δ s * δ l * ‖u s‖ * ‖u l‖ :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (hδ s).le (hδ l).le) (norm_nonneg (u s)))
        (norm_nonneg (u l))
    exact mul_le_mul_of_nonneg_left (hInner s l) hcoef
  let D : ℝ := ∑ s, ∑ l, δ s * δ l * ‖u s‖ * ‖u l‖ *
    (if s = l then (203 / 2000 : ℝ) / δ s ^ 3 else 0)
  let E : ℝ := ∑ s, ∑ l, δ s * δ l * ‖u s‖ * ‖u l‖ *
    ((811 / 2000 : ℝ) * (1 / δ s + 1 / δ l) * K s l ^ 2)
  have hD : D = 203 / 2000 := by
    calc
      D = ∑ s, δ s * δ s * ‖u s‖ * ‖u s‖ *
          ((203 / 2000 : ℝ) / δ s ^ 3) := by
        simp only [D, mul_ite, mul_zero]
        simp
      _ = (203 / 2000 : ℝ) * ∑ s, ‖u s‖ ^ 2 / δ s := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        field_simp
      _ = 203 / 2000 := by rw [hnorm, mul_one]
  have hE : E = (811 / 2000 : ℝ) * T₆ := by
    calc
      E = ∑ s, ∑ l, (811 / 2000 : ℝ) *
          ((δ s + δ l) * K s l ^ 2 * ‖u s‖ * ‖u l‖) := by
        simp only [E]
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro l _
        field_simp [hδne s, hδne l]
        ring
      _ = (811 / 2000 : ℝ) * T₆ := by
        simp only [T₆]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
  have hQ : Q ≤ 203 / 2000 + (811 / 2000 : ℝ) * T₆ := by
    calc
      Q ≤ ∑ s, ∑ l,
          δ s * δ l * ‖u s‖ * ‖u l‖ *
            ((if s = l then (203 / 2000 : ℝ) / δ s ^ 3 else 0) +
              (811 / 2000 : ℝ) * (1 / δ s + 1 / δ l) * K s l ^ 2) := hQraw
      _ = D + E := by
        simp only [D, E]
        simp_rw [mul_add, Finset.sum_add_distrib]
      _ = 203 / 2000 + (811 / 2000 : ℝ) * T₆ := by rw [hD, hE]
  have hPquad : P ^ 2 ≤ 203 / 2000 + (811 / 1000 : ℝ) * P := by
    calc
      P ^ 2 ≤ Q := hP2
      _ ≤ 203 / 2000 + (811 / 2000 : ℝ) * T₆ := hQ
      _ = 203 / 2000 + (811 / 1000 : ℝ) * P := by rw [hT₆P]; ring
  have hPbound : P ≤ 3689 / 4000 := by
    by_contra hP
    have hPlt : (3689 / 4000 : ℝ) < P := lt_of_not_ge hP
    have hprod : 0 < (P - 3689 / 4000) * (P + 89 / 800) := by positivity
    nlinarith
  have hT₆bound : T₆ ≤ 3689 / 2000 := by rw [hT₆P]; linarith
  rw [hdecomp]
  linarith

private theorem weightedMatrix_norm_le_three_halves {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (δ : ι → ℝ) (K L : ι → ι → ℝ)
    (hδ : ∀ r, 0 < δ r)
    (hK : ∀ r s, K s r = -K r s)
    (hKL : ∀ r s t,
      K r s * K r t = K s t * (L r s - L r t) +
        (if r = s then K s t * L s t else 0) +
        (if r = t then K s t * L s t else 0) +
        (if s = t then K r s ^ 2 else 0))
    (hLK : ∀ r s, |L r s| ≤ |K r s|)
    (hA : ∀ s, ∑ r, δ r * K r s ^ 2 ≤ (811 / 2000 : ℝ) / δ s)
    (hB : ∀ s, ∑ r, δ r * K r s ^ 4 ≤ (203 / 2000 : ℝ) / δ s ^ 3)
    (hC : ∀ s t, s ≠ t →
      ∑ r, δ r * K r s ^ 2 * K r t ^ 2 ≤
        (811 / 2000 : ℝ) * (1 / δ s + 1 / δ t) * K s t ^ 2) :
    ‖weightedMatrix δ K‖ ≤ 3 / 2 := by
  let hHerm : (weightedMatrix δ K).IsHermitian := weightedMatrix_isHermitian δ K hK
  apply hermitian_norm_le_of_eigenvalues_le (weightedMatrix δ K) hHerm (3 / 2)
  intro i
  let v : EuclideanSpace ℂ ι := hHerm.eigenvectorBasis i
  let u : ι → ℂ := fun r ↦ Real.sqrt (δ r) * v.ofLp r
  have hnorm : ∑ r, ‖u r‖ ^ 2 / δ r = 1 := by
    calc
      (∑ r, ‖u r‖ ^ 2 / δ r) = ∑ r, ‖v.ofLp r‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro r _
        simp only [u, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.sqrt_pos.2 (hδ r)), mul_pow]
        rw [Real.sq_sqrt (hδ r).le]
        field_simp [(hδ r).ne']
      _ = ‖v‖ ^ 2 := (EuclideanSpace.norm_sq_eq v).symm
      _ = 1 := by
        rw [hHerm.eigenvectorBasis.orthonormal.norm_eq_one i]
        norm_num
  have heig : ∀ r, ∑ s, (K r s : ℂ) * u s =
      -Complex.I * hHerm.eigenvalues i * u r / δ r := by
    intro r
    have he := congrFun (hHerm.mulVec_eigenvectorBasis i) r
    simp only [Matrix.mulVec, weightedMatrix, dotProduct, Pi.smul_apply] at he
    change (∑ s, Complex.I * Real.sqrt (δ r) * Real.sqrt (δ s) * K r s *
      v.ofLp s) = (hHerm.eigenvalues i : ℂ) * v.ofLp r at he
    simp only [u]
    have hr : (Real.sqrt (δ r) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (hδ r)).ne'
    have he' : Complex.I * Real.sqrt (δ r) *
        (∑ s, (K r s : ℂ) * (Real.sqrt (δ s) * v.ofLp s)) =
        (hHerm.eigenvalues i : ℂ) * v.ofLp r := by
      rw [Finset.mul_sum]
      calc
        (∑ s, Complex.I * Real.sqrt (δ r) *
            ((K r s : ℂ) * (Real.sqrt (δ s) * v.ofLp s))) =
            ∑ s, Complex.I * Real.sqrt (δ r) * Real.sqrt (δ s) *
              K r s * v.ofLp s := by
          apply Finset.sum_congr rfl
          intro s _
          ring
        _ = (hHerm.eigenvalues i : ℂ) * v.ofLp r := he
    calc
      (∑ s, (K r s : ℂ) * (Real.sqrt (δ s) * v.ofLp s)) =
          (-Complex.I / Real.sqrt (δ r)) *
            (Complex.I * Real.sqrt (δ r) *
              ∑ s, (K r s : ℂ) * (Real.sqrt (δ s) * v.ofLp s)) := by
        field_simp [hr]
        rw [Complex.I_sq]
        ring
      _ = (-Complex.I / Real.sqrt (δ r)) *
          ((hHerm.eigenvalues i : ℂ) * v.ofLp r) := by rw [he']
      _ = -Complex.I * hHerm.eigenvalues i *
          (Real.sqrt (δ r) * v.ofLp r) / δ r := by
        rw [show ((δ r : ℝ) : ℂ) = (Real.sqrt (δ r) : ℂ) ^ 2 by
          exact_mod_cast (Real.sq_sqrt (hδ r).le).symm]
        field_simp [hr]
  have hsquare : hHerm.eigenvalues i ^ 2 ≤ 9 / 4 :=
    weightedKernel_eigenvalue_sq_le δ K L u (hHerm.eigenvalues i)
      hδ hK hKL hLK hA hB hC hnorm heig
  rw [← sq_abs] at hsquare
  nlinarith [abs_nonneg (hHerm.eigenvalues i)]

private noncomputable def cosecantKernel {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ) (r s : ι) : ℝ :=
  if r = s then 0 else 1 / Real.sin (Real.pi * (x r - x s))

private noncomputable def cotangentKernel {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ) (r s : ι) : ℝ :=
  if r = s then 0 else
    Real.cos (Real.pi * (x r - x s)) / Real.sin (Real.pi * (x r - x s))

private theorem cosecantKernel_skew {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ) (r s : ι) :
    cosecantKernel x s r = -cosecantKernel x r s := by
  by_cases hrs : r = s
  · subst s
    simp [cosecantKernel]
  · simp only [cosecantKernel, hrs, Ne.symm hrs, ite_false]
    rw [show x s - x r = -(x r - x s) by ring, mul_neg, Real.sin_neg]
    ring

private theorem cotangentKernel_skew {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ) (r s : ι) :
    cotangentKernel x s r = -cotangentKernel x r s := by
  by_cases hrs : r = s
  · subst s
    simp [cotangentKernel]
  · simp only [cotangentKernel, hrs, Ne.symm hrs, ite_false]
    rw [show x s - x r = -(x r - x s) by ring, mul_neg, Real.sin_neg,
      Real.cos_neg]
    ring

private theorem cotangentKernel_abs_le_cosecantKernel_abs {ι : Type*}
    [DecidableEq ι] (x : ι → ℝ) (r s : ι) :
    |cotangentKernel x r s| ≤ |cosecantKernel x r s| := by
  by_cases hrs : r = s
  · subst s
    simp [cotangentKernel, cosecantKernel]
  · simp only [cotangentKernel, cosecantKernel, hrs, ite_false, abs_div, abs_one]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _)

private theorem cosecantKernel_mul_identity {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ)
    (hsin : ∀ r s, r ≠ s → Real.sin (Real.pi * (x r - x s)) ≠ 0)
    (r s t : ι) :
    cosecantKernel x r s * cosecantKernel x r t =
      cosecantKernel x s t * (cotangentKernel x r s - cotangentKernel x r t) +
        (if r = s then cosecantKernel x s t * cotangentKernel x s t else 0) +
        (if r = t then cosecantKernel x s t * cotangentKernel x s t else 0) +
        (if s = t then cosecantKernel x r s ^ 2 else 0) := by
  by_cases hrs : r = s
  · subst s
    by_cases hrt : r = t
    · subst t
      simp [cosecantKernel, cotangentKernel]
    · simp only [ite_true, hrt, ite_false]
      rw [show cosecantKernel x r r = 0 by simp [cosecantKernel],
        show cotangentKernel x r r = 0 by simp [cotangentKernel]]
      ring
  by_cases hrt : r = t
  · subst t
    simp only [ite_true, hrs, Ne.symm hrs, ite_false]
    rw [show cosecantKernel x r r = 0 by simp [cosecantKernel],
      show cotangentKernel x r r = 0 by simp [cotangentKernel],
      cosecantKernel_skew x r s, cotangentKernel_skew x r s]
    ring
  by_cases hst : s = t
  · subst t
    simp only [ite_true, hrs, ite_false]
    rw [show cosecantKernel x s s = 0 by simp [cosecantKernel]]
    ring
  simp only [hrs, hrt, hst, ite_false, add_zero, cosecantKernel, cotangentKernel]
  have hrsin := hsin r s hrs
  have hrtin := hsin r t hrt
  have hstin := hsin s t hst
  field_simp [hrsin, hrtin, hstin]
  rw [show Real.pi * (x s - x t) =
    Real.pi * (x r - x t) - Real.pi * (x r - x s) by ring, Real.sin_sub]
  ring

private theorem sine_ne_zero_of_circle_separated {ι : Type*}
    (x δ : ι → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s, r ≠ s →
      δ r ≤ ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖)
    (r s : ι) (hrs : r ≠ s) :
    Real.sin (Real.pi * (x r - x s)) ≠ 0 := by
  have hnorm : 0 < ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖ :=
    (hδ r).trans_le (hsep r s hrs)
  have hcircle : ((x r - x s : ℝ) : AddCircle (1 : ℝ)) ≠ 0 := by
    simpa only [norm_pos_iff] using hnorm
  intro hsin
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
  have hn' : (n : ℝ) = x r - x s := by
    have hpi := Real.pi_pos
    nlinarith
  apply hcircle
  rw [← hn']
  simp

private theorem two_circle_norm_le_abs_sin_pi (d : ℝ) :
    2 * ‖(d : AddCircle (1 : ℝ))‖ ≤ |Real.sin (Real.pi * d)| := by
  let y : ℝ := (AddCircle.equivIco (1 : ℝ) (-1 / 2 : ℝ)
    (d : AddCircle (1 : ℝ))).1
  have hy_mem : y ∈ Set.Ico (-1 / 2 : ℝ) (-1 / 2 + 1) :=
    (AddCircle.equivIco (1 : ℝ) (-1 / 2 : ℝ)
      (d : AddCircle (1 : ℝ))).2
  have hyabs : |y| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hy_mem.1, hy_mem.2]
  have hycoe : (y : AddCircle (1 : ℝ)) = (d : AddCircle (1 : ℝ)) :=
    AddCircle.coe_equivIco
  have hynorm : ‖(d : AddCircle (1 : ℝ))‖ = |y| := by
    rw [← hycoe]
    exact (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).2 (by simpa using hyabs)
  have hyarg : |Real.pi * y| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hJordan := Real.mul_abs_le_abs_sin hyarg
  have hySin : 2 * |y| ≤ |Real.sin (Real.pi * y)| := by
    calc
      2 * |y| = 2 / Real.pi * |Real.pi * y| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        field_simp [Real.pi_ne_zero]
      _ ≤ |Real.sin (Real.pi * y)| := hJordan
  have hzero : ((d - y : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub]
    simp [hycoe]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  have hn' : (n : ℝ) = d - y := by simpa using hn
  have hsin : |Real.sin (Real.pi * d)| = |Real.sin (Real.pi * y)| := by
    rw [show Real.pi * d = Real.pi * y + (n : ℝ) * Real.pi by
      rw [hn']; ring, Real.sin_add_int_mul_pi]
    simp
  rw [hynorm, hsin]
  exact hySin

private theorem cosecantKernel_sq_le {ι : Type*} [DecidableEq ι]
    (x δ : ι → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s, r ≠ s →
      δ r ≤ ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖)
    (r s : ι) :
    cosecantKernel x r s ^ 2 ≤ 1 / (4 * δ s ^ 2) := by
  by_cases hrs : r = s
  · subst s
    have hdiag : cosecantKernel x r r = 0 := by simp [cosecantKernel]
    rw [hdiag]
    norm_num
    positivity
  have hdist := hsep s r (Ne.symm hrs)
  have hdist' : δ s ≤ ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖ := by
    simpa only [AddCircle.coe_sub] using hdist.trans_eq
      (norm_sub_rev ((x s : ℝ) : AddCircle (1 : ℝ))
        ((x r : ℝ) : AddCircle (1 : ℝ)))
  have hsin := two_circle_norm_le_abs_sin_pi (x r - x s)
  have hlower : 2 * δ s ≤ |Real.sin (Real.pi * (x r - x s))| := by linarith
  have hsq : (2 * δ s) ^ 2 ≤ |Real.sin (Real.pi * (x r - x s))| ^ 2 :=
    pow_le_pow_left₀ (by nlinarith [hδ s]) hlower 2
  have hinv := one_div_le_one_div_of_le
    (sq_pos_of_pos (by nlinarith [hδ s] : 0 < 2 * δ s)) hsq
  simp only [cosecantKernel, hrs, ite_false, div_pow, one_pow]
  rw [sq_abs] at hinv
  convert hinv using 1
  all_goals ring

private theorem cosecantKernel_sq_sum_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] (x δ : ι → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s, r ≠ s →
      δ r ≤ ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖) (s : ι) :
    ∑ r, δ r * cosecantKernel x r s ^ 2 ≤
      (811 / 2000 : ℝ) / δ s := by
  have hsumErase :
      (∑ r, δ r * cosecantKernel x r s ^ 2) =
        ∑ r ∈ Finset.univ.erase s, δ r * cosecantKernel x r s ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s)]
    simp [cosecantKernel]
  rw [hsumErase]
  calc
    (∑ r ∈ Finset.univ.erase s, δ r * cosecantKernel x r s ^ 2) =
        ∑ r ∈ Finset.univ.erase s, δ r * cscSq (circleCoord x s r) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrs : r ≠ s := (Finset.mem_erase.mp hr).1
      simp only [cosecantKernel, hrs, ite_false, cscSq, div_pow, one_pow]
      rw [sin_pi_circleCoord_sq x s r]
    _ ≤ 4 / (Real.pi ^ 2 * δ s) := circle_cscSq_sum_le x δ hδ hsep s
    _ = (4 / Real.pi ^ 2) / δ s := by
      field_simp [Real.pi_ne_zero, (hδ s).ne']
    _ ≤ (811 / 2000 : ℝ) / δ s := by
      apply div_le_div_of_nonneg_right _ (hδ s).le
      rw [div_le_iff₀ (sq_pos_of_pos Real.pi_pos)]
      have hp := Real.pi_gt_d4
      have hprod : 0 < (Real.pi - 3.1415) * (Real.pi + 3.1415) := by
        positivity
      nlinarith

private theorem cosecantKernel_fourth_sum_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] (x δ : ι → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s, r ≠ s →
      δ r ≤ ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖)
    (hA : ∀ s, ∑ r, δ r * cosecantKernel x r s ^ 2 ≤
      (811 / 2000 : ℝ) / δ s) (s : ι) :
    ∑ r, δ r * cosecantKernel x r s ^ 4 ≤
      (203 / 2000 : ℝ) / δ s ^ 3 := by
  calc
    (∑ r, δ r * cosecantKernel x r s ^ 4) =
        ∑ r, δ r * cosecantKernel x r s ^ 2 * cosecantKernel x r s ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ ≤ ∑ r, δ r * (1 / (4 * δ s ^ 2)) * cosecantKernel x r s ^ 2 := by
      apply Finset.sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (cosecantKernel_sq_le x δ hδ hsep r s)
          (hδ r).le)
        (sq_nonneg _)
    _ = (1 / (4 * δ s ^ 2)) *
        ∑ r, δ r * cosecantKernel x r s ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ ≤ (1 / (4 * δ s ^ 2)) * ((811 / 2000 : ℝ) / δ s) := by
      gcongr
      exact hA s
    _ ≤ (203 / 2000 : ℝ) / δ s ^ 3 := by
      have hs := hδ s
      field_simp
      nlinarith

private theorem cosecantKernel_product_sum_le {ι : Type*} [Fintype ι]
    [DecidableEq ι] (x δ : ι → ℝ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s, r ≠ s →
      δ r ≤ ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖)
    (s t : ι) (hst : s ≠ t) :
    ∑ r, δ r * cosecantKernel x r s ^ 2 * cosecantKernel x r t ^ 2 ≤
      (811 / 2000 : ℝ) * (1 / δ s + 1 / δ t) * cosecantKernel x s t ^ 2 := by
  have htmem : t ∈ Finset.univ.erase s :=
    Finset.mem_erase.mpr ⟨Ne.symm hst, Finset.mem_univ t⟩
  have hsum :
      (∑ r, δ r * cosecantKernel x r s ^ 2 * cosecantKernel x r t ^ 2) =
        ∑ r ∈ (Finset.univ.erase s).erase t,
          δ r * cosecantKernel x r s ^ 2 * cosecantKernel x r t ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ s)]
    simp only [cosecantKernel, ↓reduceIte]
    rw [← Finset.sum_erase_add _ _ htmem]
    simp
  have hconvert :
      (∑ r ∈ (Finset.univ.erase s).erase t,
          δ r * cosecantKernel x r s ^ 2 * cosecantKernel x r t ^ 2) =
        ∑ r ∈ (Finset.univ.erase s).erase t,
          δ r * cscSqProduct (circleCoord x s t) (circleCoord x s r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrs : r ≠ s := (Finset.mem_erase.mp (Finset.mem_erase.mp hr).2).1
    have hrt : r ≠ t := (Finset.mem_erase.mp hr).1
    simp only [cosecantKernel, hrs, hrt, ite_false, cscSqProduct, cscSq,
      div_pow, one_pow]
    rw [sin_pi_circleCoord_sq x s r, sin_pi_circleCoord_sub_sq x s r t]
    ring
  have hKst : cscSq (circleCoord x s t) = cosecantKernel x s t ^ 2 := by
    simp only [cscSq, cosecantKernel, hst, ite_false, div_pow, one_pow]
    rw [← sin_pi_circleCoord_sq x s t]
    rw [show x t - x s = -(x s - x t) by ring, mul_neg, Real.sin_neg]
    ring
  calc
    (∑ r, δ r * cosecantKernel x r s ^ 2 * cosecantKernel x r t ^ 2) =
        ∑ r ∈ (Finset.univ.erase s).erase t,
          δ r * cscSqProduct (circleCoord x s t) (circleCoord x s r) := by
      rw [hsum, hconvert]
    _ ≤ 4 / Real.pi ^ 2 * (1 / δ s + 1 / δ t) *
        cscSq (circleCoord x s t) :=
      circle_cscSqProduct_sum_le x δ hδ hsep s t hst
    _ = 4 / Real.pi ^ 2 * (1 / δ s + 1 / δ t) *
        cosecantKernel x s t ^ 2 := by rw [hKst]
    _ ≤ (811 / 2000 : ℝ) * (1 / δ s + 1 / δ t) *
        cosecantKernel x s t ^ 2 := by
      have hp : 4 / Real.pi ^ 2 ≤ (811 / 2000 : ℝ) := by
        rw [div_le_iff₀ (sq_pos_of_pos Real.pi_pos)]
        have hpi := Real.pi_gt_d4
        have hprod : 0 < (Real.pi - 3.1415) * (Real.pi + 3.1415) := by
          positivity
        nlinarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp
          (add_nonneg (one_div_nonneg.mpr (hδ s).le)
            (one_div_nonneg.mpr (hδ t).le)))
        (sq_nonneg _)

/--
**The Montgomery–Vaughan weighted Hilbert inequality.** Let $\iota$ be a finite index set and
for $r \in \iota$ let $x_r$ and $\delta_r > 0$ be real numbers and $z_r$ a complex number. Write
$\|t\|$ for the distance from a real number $t$ to the nearest integer, and suppose that
$\delta_r \le \|x_r - x_s\|$ for all $r \ne s$. Then
$$
\left| \sum_{r} \sum_{s \ne r} \frac{z_r \overline{z_s}}{\sin(\pi (x_r - x_s))} \right| \le
\frac{3}{2} \sum_{r} \frac{|z_r|^2}{\delta_r}.
$$

Source: Montgomery–Vaughan (1974), Theorem 1, in its weighted circle form. The
proof follows Yangjit, arXiv:2203.14950, lines 166–205, 209–462, and 596–640:
Selberg's eigenvector identity, the Hermitian spectral theorem, and convex circle
packing estimates for the one-pole and two-pole cosecant-square sums.
-/
public theorem weightedHilbertCosecant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x δ : ι → ℝ) (z : ι → ℂ) (hδ : ∀ r, 0 < δ r)
    (hsep : ∀ r s, r ≠ s →
      δ r ≤ ‖((x r - x s : ℝ) : AddCircle (1 : ℝ))‖) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r,
        z r * conj (z s) / Real.sin (Real.pi * (x r - x s))‖ ≤
      3 / 2 * ∑ r, ‖z r‖ ^ 2 / δ r := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · have hsin : ∀ r s, r ≠ s → Real.sin (Real.pi * (x r - x s)) ≠ 0 :=
      sine_ne_zero_of_circle_separated x δ hδ hsep
    have hA : ∀ s, ∑ r, δ r * cosecantKernel x r s ^ 2 ≤
        (811 / 2000 : ℝ) / δ s :=
      cosecantKernel_sq_sum_le x δ hδ hsep
    have hB : ∀ s, ∑ r, δ r * cosecantKernel x r s ^ 4 ≤
        (203 / 2000 : ℝ) / δ s ^ 3 :=
      cosecantKernel_fourth_sum_le x δ hδ hsep hA
    have hC : ∀ s t, s ≠ t →
        ∑ r, δ r * cosecantKernel x r s ^ 2 * cosecantKernel x r t ^ 2 ≤
          (811 / 2000 : ℝ) * (1 / δ s + 1 / δ t) *
            cosecantKernel x s t ^ 2 :=
      cosecantKernel_product_sum_le x δ hδ hsep
    have hmatrix : ‖weightedMatrix δ (cosecantKernel x)‖ ≤ 3 / 2 :=
      weightedMatrix_norm_le_three_halves δ (cosecantKernel x) (cotangentKernel x)
        hδ (cosecantKernel_skew x) (cosecantKernel_mul_identity x hsin)
        (cotangentKernel_abs_le_cosecantKernel_abs x) hA hB hC
    have hsum :
        (∑ r, ∑ s ∈ Finset.univ.erase r,
            z r * conj (z s) / Real.sin (Real.pi * (x r - x s))) =
          ∑ r, ∑ s, z r * conj (z s) * cosecantKernel x r s := by
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ r)]
      simp only [cosecantKernel, ↓reduceIte, Complex.ofReal_zero, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro s hs
      have hrs : s ≠ r := (Finset.mem_erase.mp hs).1
      have hrs' : r ≠ s := Ne.symm hrs
      simp only [hrs', ite_false]
      push_cast
      ring
    rw [hsum]
    exact bilinear_le_of_weightedMatrix_norm δ (cosecantKernel x) (3 / 2)
      hδ z hmatrix

end MathlibExt.NumberTheory.PrimeCounting
