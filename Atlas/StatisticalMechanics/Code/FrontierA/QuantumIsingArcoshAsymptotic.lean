/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.QuantumIsingSymbolAsymptotic
import Mathlib.Analysis.SpecialFunctions.Arcosh










open Filter Set Topology
open scoped Topology

namespace StatMech.FrontierA



noncomputable def arcoshQuadraticRatio (u : Real) : Real :=
  if u = 0 then 2 else u ^ 2 / (Real.cosh u - 1)

theorem arcoshQuadraticRatio_tendsto_two :
    Tendsto arcoshQuadraticRatio (nhdsWithin 0 (Ici 0)) (nhds 2) := by
  have hrightInv := cosh_sub_one_div_sq_tendsto_half_right.inv₀
    (by norm_num : (1 / 2 : Real) ≠ 0)
  have hright : Tendsto (fun u : Real => u ^ 2 / (Real.cosh u - 1))
      (nhdsWithin 0 (Ioi 0)) (nhds 2) := by
    have hright' : Tendsto (fun u : Real => u ^ 2 / (Real.cosh u - 1))
        (nhdsWithin 0 (Ioi 0)) (nhds (2 / 1 : Real)) := by
      simpa only [inv_div] using hrightInv
    norm_num at hright'
    exact hright'
  have hIci : Ici (0 : Real) = {0} ∪ Ioi 0 := by
    ext u
    simp only [mem_Ici, mem_union, mem_singleton_iff, mem_Ioi]
    constructor
    · intro hu
      rcases hu.eq_or_lt with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (rfl | hu)
      · exact le_rfl
      · exact hu.le
  rw [hIci, nhdsWithin_union, tendsto_sup]
  constructor
  · simpa [nhdsWithin_singleton, arcoshQuadraticRatio] using
      (tendsto_pure_nhds arcoshQuadraticRatio (0 : Real))
  · apply hright.congr'
    filter_upwards [self_mem_nhdsWithin] with u hu
    change 0 < u at hu
    simp [arcoshQuadraticRatio, hu.ne']



theorem continuousOn_arcoshQuadraticRatio :
    ContinuousOn arcoshQuadraticRatio (Ici 0) := by
  intro u hu
  by_cases hu0 : u = 0
  · subst u
    change Tendsto arcoshQuadraticRatio (nhdsWithin 0 (Ici 0))
      (nhds (arcoshQuadraticRatio 0))
    simpa [arcoshQuadraticRatio] using arcoshQuadraticRatio_tendsto_two
  · have hcosh : Real.cosh u - 1 ≠ 0 := by
      have : 1 < Real.cosh u := Real.one_lt_cosh.mpr hu0
      linarith
    have hcont : ContinuousAt
        (fun x : Real => x ^ 2 / (Real.cosh x - 1)) u := by
      fun_prop
    refine hcont.continuousWithinAt.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [(eventually_ne_nhds hu0).filter_mono inf_le_left] with x hx
      simp only [arcoshQuadraticRatio, if_neg hx]
    · simp [arcoshQuadraticRatio, hu0]

theorem arcoshQuadraticRatio_pos {u : Real} (hu : 0 <= u) :
    0 < arcoshQuadraticRatio u := by
  by_cases hu0 : u = 0
  · simp [arcoshQuadraticRatio, hu0]
  · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    have hcosh : 0 < Real.cosh u - 1 := sub_pos.mpr
      (Real.one_lt_cosh.mpr hu0)
    simp only [arcoshQuadraticRatio, if_neg hu0]
    exact div_pos (sq_pos_of_pos hupos) hcosh


theorem scaled_arcosh_sq_eq_ratio
    (scale A : Real) (hA : 1 <= A) :
    (scale * Real.arcosh A) ^ 2 =
      arcoshQuadraticRatio (Real.arcosh A) *
        (scale ^ 2 * (A - 1)) := by
  let u := Real.arcosh A
  change (scale * u) ^ 2 =
    arcoshQuadraticRatio u * (scale ^ 2 * (A - 1))
  by_cases hu0 : u = 0
  · have hA1 : A = 1 := (Real.arcosh_eq_zero_iff hA).mp hu0
    simp [hu0, hA1, arcoshQuadraticRatio]
  · have hcosh : Real.cosh u = A := Real.cosh_arcosh hA
    have hden : Real.cosh u - 1 ≠ 0 := by
      rw [hcosh]
      exact sub_ne_zero.mpr ((Real.arcosh_eq_zero_iff hA).not.mp hu0)
    rw [show A - 1 = Real.cosh u - 1 by rw [hcosh]]
    simp only [arcoshQuadraticRatio, if_neg hu0]
    field_simp [hden]




theorem arcosh_scaled_tendsto_sqrt
    (A : Nat -> Real) {c : Real}
    (hscaled : Tendsto
      (fun n : Nat => (n + 1 : Real) ^ 2 * (A n - 1))
      atTop (nhds c))
    (hbranch : ∀ᶠ n in atTop, 1 <= A n) :
    Tendsto (fun n : Nat => (n + 1 : Real) * Real.arcosh (A n))
      atTop (nhds (Real.sqrt (2 * c))) := by
  let scale : Nat -> Real := fun n => (n + 1 : Real)
  let u : Nat -> Real := fun n => Real.arcosh (A n)
  have hInv : Tendsto (fun n : Nat => (scale n)⁻¹) atTop (nhds 0) := by
    simpa only [scale, Nat.cast_add, Nat.cast_one, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hInvSq : Tendsto (fun n : Nat => (scale n)⁻¹ ^ 2)
      atTop (nhds 0) := by
    simpa using hInv.pow 2
  have hsub : Tendsto (fun n => A n - 1) atTop (nhds 0) := by
    have hmul := hInvSq.mul hscaled
    convert hmul using 1
    · funext n
      dsimp only [scale]
      have hs : scale n ≠ 0 := by
        dsimp only [scale]
        positivity
      dsimp only [scale] at hs
      field_simp [hs]
    · ring
  have hA : Tendsto A atTop (nhds 1) := by
    have hadd := hsub.const_add 1
    convert hadd using 1 <;> ring
  have hAWithin : Tendsto A atTop (nhdsWithin 1 (Ici 1)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hA, hbranch⟩
  have hu : Tendsto u atTop (nhds 0) := by
    have hcont := Real.continuousOn_arcosh.continuousWithinAt
      (show (1 : Real) ∈ Ici 1 by simp)
    simpa only [u, Real.arcosh_zero] using hcont.tendsto.comp hAWithin
  have huNonneg : ∀ᶠ n in atTop, 0 <= u n := by
    filter_upwards [hbranch] with n hn
    exact Real.arcosh_nonneg hn
  have huWithin : Tendsto u atTop (nhdsWithin 0 (Ici 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hu, huNonneg⟩
  have hratio : Tendsto (fun n => arcoshQuadraticRatio (u n))
      atTop (nhds 2) :=
    arcoshQuadraticRatio_tendsto_two.comp huWithin
  have hsq : Tendsto (fun n => (scale n * u n) ^ 2)
      atTop (nhds (2 * c)) := by
    have hprod := hratio.mul hscaled
    apply hprod.congr'
    filter_upwards [hbranch] with n hn
    by_cases hu0 : u n = 0
    · have hA1 : A n = 1 :=
        (Real.arcosh_eq_zero_iff hn).mp hu0
      simp [arcoshQuadraticRatio, hu0, hA1]
    · have hcosh : Real.cosh (u n) = A n := by
        exact Real.cosh_arcosh hn
      have hden : Real.cosh (u n) - 1 ≠ 0 := by
        rw [hcosh]
        exact sub_ne_zero.mpr ((Real.arcosh_eq_zero_iff hn).not.mp hu0)
      rw [show A n - 1 = Real.cosh (u n) - 1 by rw [hcosh]]
      simp only [arcoshQuadraticRatio, if_neg hu0]
      field_simp [hden]
      ring
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  apply hsqrt.congr'
  filter_upwards [hbranch] with n hn
  simp only [Function.comp_apply]
  rw [Real.sqrt_sq]
  exact mul_nonneg (by
    dsimp only [scale]
    positivity) (Real.arcosh_nonneg hn)

end StatMech.FrontierA
