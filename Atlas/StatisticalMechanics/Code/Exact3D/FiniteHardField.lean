/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib










open Filter
open scoped BigOperators Topology

namespace StatMech
namespace Exact3D




noncomputable def finiteFactorNumerator {α : Type*} (s : Finset α)
    (base obs : α → ℝ) (factor : ℝ → α → ℝ) (H : ℝ) : ℝ :=
  ∑ a ∈ s, base a * factor H a * obs a


noncomputable def finiteFactorDenominator {α : Type*} (s : Finset α)
    (base : α → ℝ) (factor : ℝ → α → ℝ) (H : ℝ) : ℝ :=
  ∑ a ∈ s, base a * factor H a


noncomputable def finiteFactorLimitNumerator {α : Type*} (s : Finset α)
    (base obs limitFactor : α → ℝ) : ℝ :=
  ∑ a ∈ s, base a * limitFactor a * obs a


noncomputable def finiteFactorLimitDenominator {α : Type*} (s : Finset α)
    (base limitFactor : α → ℝ) : ℝ :=
  ∑ a ∈ s, base a * limitFactor a


noncomputable def finiteFactorRatio {α : Type*} (s : Finset α)
    (base obs : α → ℝ) (factor : ℝ → α → ℝ) (H : ℝ) : ℝ :=
  finiteFactorNumerator s base obs factor H /
    finiteFactorDenominator s base factor H


noncomputable def finiteFactorLimitRatio {α : Type*} (s : Finset α)
    (base obs limitFactor : α → ℝ) : ℝ :=
  finiteFactorLimitNumerator s base obs limitFactor /
    finiteFactorLimitDenominator s base limitFactor


theorem finiteFactorNumeratorSummand_tendsto {α : Type*}
    (base obs limitFactor : α → ℝ) (factor : ℝ → α → ℝ) (a : α)
    (hfactor : Tendsto (fun H : ℝ => factor H a) atTop (𝓝 (limitFactor a))) :
    Tendsto (fun H : ℝ => base a * factor H a * obs a)
      atTop
      (𝓝 (base a * limitFactor a * obs a)) := by
  have hmul :
      Tendsto (fun H : ℝ => (base a * obs a) * factor H a)
        atTop
        (𝓝 ((base a * obs a) * limitFactor a)) :=
    Filter.Tendsto.const_mul (base a * obs a) hfactor
  have hrewrite :
      (fun H : ℝ => base a * factor H a * obs a)
        =
      (fun H : ℝ => (base a * obs a) * factor H a) := by
    funext H
    ring
  have htarget : (base a * obs a) * limitFactor a =
      base a * limitFactor a * obs a := by
    ring
  simpa [hrewrite, htarget] using hmul


theorem finiteFactorDenominatorSummand_tendsto {α : Type*}
    (base limitFactor : α → ℝ) (factor : ℝ → α → ℝ) (a : α)
    (hfactor : Tendsto (fun H : ℝ => factor H a) atTop (𝓝 (limitFactor a))) :
    Tendsto (fun H : ℝ => base a * factor H a)
      atTop
      (𝓝 (base a * limitFactor a)) :=
  Filter.Tendsto.const_mul (base a) hfactor


theorem finiteFactorNumerator_tendsto {α : Type*} (s : Finset α)
    (base obs limitFactor : α → ℝ) (factor : ℝ → α → ℝ)
    (hfactor :
      ∀ a, a ∈ s →
        Tendsto (fun H : ℝ => factor H a) atTop (𝓝 (limitFactor a))) :
    Tendsto (fun H : ℝ => finiteFactorNumerator s base obs factor H)
      atTop
      (𝓝 (finiteFactorLimitNumerator s base obs limitFactor)) := by
  unfold finiteFactorNumerator finiteFactorLimitNumerator
  exact tendsto_finsetSum s (fun a ha =>
    finiteFactorNumeratorSummand_tendsto base obs limitFactor factor a
      (hfactor a ha))


theorem finiteFactorDenominator_tendsto {α : Type*} (s : Finset α)
    (base limitFactor : α → ℝ) (factor : ℝ → α → ℝ)
    (hfactor :
      ∀ a, a ∈ s →
        Tendsto (fun H : ℝ => factor H a) atTop (𝓝 (limitFactor a))) :
    Tendsto (fun H : ℝ => finiteFactorDenominator s base factor H)
      atTop
      (𝓝 (finiteFactorLimitDenominator s base limitFactor)) := by
  unfold finiteFactorDenominator finiteFactorLimitDenominator
  exact tendsto_finsetSum s (fun a ha =>
    finiteFactorDenominatorSummand_tendsto base limitFactor factor a
      (hfactor a ha))



theorem finiteFactorRatio_tendsto {α : Type*} (s : Finset α)
    (base obs limitFactor : α → ℝ) (factor : ℝ → α → ℝ)
    (hfactor :
      ∀ a, a ∈ s →
        Tendsto (fun H : ℝ => factor H a) atTop (𝓝 (limitFactor a)))
    (hden : finiteFactorLimitDenominator s base limitFactor ≠ 0) :
    Tendsto (fun H : ℝ => finiteFactorRatio s base obs factor H)
      atTop
      (𝓝 (finiteFactorLimitRatio s base obs limitFactor)) := by
  unfold finiteFactorRatio finiteFactorLimitRatio
  exact Filter.Tendsto.div
    (finiteFactorNumerator_tendsto s base obs limitFactor factor hfactor)
    (finiteFactorDenominator_tendsto s base limitFactor factor hfactor)
    hden




noncomputable def hardFieldFactor {α : Type*} (good : α → Prop)
    [DecidablePred good] (H : ℝ) (a : α) : ℝ :=
  if good a then 1 else Real.exp (-H)


noncomputable def hardFieldNumerator {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base obs : α → ℝ)
    (H : ℝ) : ℝ :=
  ∑ a ∈ s, base a * hardFieldFactor good H a * obs a


noncomputable def hardFieldDenominator {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base : α → ℝ)
    (H : ℝ) : ℝ :=
  ∑ a ∈ s, base a * hardFieldFactor good H a



noncomputable def hardFieldLimitNumerator {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base obs : α → ℝ) : ℝ :=
  ∑ a ∈ s, if good a then base a * obs a else 0



noncomputable def hardFieldLimitDenominator {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base : α → ℝ) : ℝ :=
  ∑ a ∈ s, if good a then base a else 0


noncomputable def hardFieldRatio {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base obs : α → ℝ)
    (H : ℝ) : ℝ :=
  hardFieldNumerator s good base obs H /
    hardFieldDenominator s good base H


noncomputable def hardFieldLimitRatio {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base obs : α → ℝ) : ℝ :=
  hardFieldLimitNumerator s good base obs /
    hardFieldLimitDenominator s good base


theorem tendsto_exp_neg_atTop :
    Tendsto (fun H : ℝ => Real.exp (-H)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp Filter.tendsto_neg_atTop_atBot


theorem hardFieldFactor_tendsto {α : Type*} (good : α → Prop)
    [DecidablePred good] (a : α) :
    Tendsto (fun H : ℝ => hardFieldFactor good H a) atTop
      (𝓝 (if good a then 1 else 0)) := by
  by_cases ha : good a
  · simp [hardFieldFactor, ha]
  · simpa [hardFieldFactor, ha] using tendsto_exp_neg_atTop


theorem hardFieldNumeratorSummand_tendsto {α : Type*}
    (good : α → Prop) [DecidablePred good] (base obs : α → ℝ) (a : α) :
    Tendsto
      (fun H : ℝ => base a * hardFieldFactor good H a * obs a)
      atTop
      (𝓝 (if good a then base a * obs a else 0)) := by
  by_cases ha : good a
  · simp [hardFieldFactor, ha]
  · have hfactor :
        Tendsto (fun H : ℝ => hardFieldFactor good H a) atTop (𝓝 0) := by
      simpa [hardFieldFactor, ha] using tendsto_exp_neg_atTop
    have hmul :
        Tendsto
          (fun H : ℝ => (base a * obs a) * hardFieldFactor good H a)
          atTop
          (𝓝 ((base a * obs a) * 0)) :=
      Filter.Tendsto.const_mul (base a * obs a) hfactor
    have hrewrite :
        (fun H : ℝ => base a * hardFieldFactor good H a * obs a)
          =
        (fun H : ℝ => (base a * obs a) * hardFieldFactor good H a) := by
      funext H
      ring
    simpa [ha, hrewrite] using hmul


theorem hardFieldDenominatorSummand_tendsto {α : Type*}
    (good : α → Prop) [DecidablePred good] (base : α → ℝ) (a : α) :
    Tendsto
      (fun H : ℝ => base a * hardFieldFactor good H a)
      atTop
      (𝓝 (if good a then base a else 0)) := by
  by_cases ha : good a
  · simp [hardFieldFactor, ha]
  · have hfactor :
        Tendsto (fun H : ℝ => hardFieldFactor good H a) atTop (𝓝 0) := by
      simpa [hardFieldFactor, ha] using tendsto_exp_neg_atTop
    have hmul :
        Tendsto
          (fun H : ℝ => base a * hardFieldFactor good H a)
          atTop
          (𝓝 (base a * 0)) :=
      Filter.Tendsto.const_mul (base a) hfactor
    simpa [ha] using hmul



theorem hardFieldNumerator_tendsto {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base obs : α → ℝ) :
    Tendsto (fun H : ℝ => hardFieldNumerator s good base obs H)
      atTop
      (𝓝 (hardFieldLimitNumerator s good base obs)) := by
  unfold hardFieldNumerator hardFieldLimitNumerator
  exact tendsto_finsetSum s (fun a _ =>
    hardFieldNumeratorSummand_tendsto good base obs a)



theorem hardFieldDenominator_tendsto {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base : α → ℝ) :
    Tendsto (fun H : ℝ => hardFieldDenominator s good base H)
      atTop
      (𝓝 (hardFieldLimitDenominator s good base)) := by
  unfold hardFieldDenominator hardFieldLimitDenominator
  exact tendsto_finsetSum s (fun a _ =>
    hardFieldDenominatorSummand_tendsto good base a)




theorem hardFieldRatio_tendsto {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base obs : α → ℝ)
    (hden : hardFieldLimitDenominator s good base ≠ 0) :
    Tendsto (fun H : ℝ => hardFieldRatio s good base obs H)
      atTop
      (𝓝 (hardFieldLimitRatio s good base obs)) := by
  unfold hardFieldRatio hardFieldLimitRatio
  exact Filter.Tendsto.div
    (hardFieldNumerator_tendsto s good base obs)
    (hardFieldDenominator_tendsto s good base)
    hden



theorem hardFieldLimitNumerator_eq_filter {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base obs : α → ℝ) :
    hardFieldLimitNumerator s good base obs =
      ∑ a ∈ s.filter good, base a * obs a := by
  classical
  unfold hardFieldLimitNumerator
  rw [← Finset.sum_filter]



theorem hardFieldLimitDenominator_eq_filter {α : Type*} (s : Finset α)
    (good : α → Prop) [DecidablePred good] (base : α → ℝ) :
    hardFieldLimitDenominator s good base =
      ∑ a ∈ s.filter good, base a := by
  classical
  unfold hardFieldLimitDenominator
  rw [← Finset.sum_filter]



theorem hardFieldLimitDenominator_pos_of_exists_pos {α : Type*}
    (s : Finset α) (good : α → Prop) [DecidablePred good] (base : α → ℝ)
    (hnonneg : ∀ a, a ∈ s → good a → 0 ≤ base a)
    (hpos : ∃ a, a ∈ s ∧ good a ∧ 0 < base a) :
    0 < hardFieldLimitDenominator s good base := by
  classical
  rw [hardFieldLimitDenominator_eq_filter]
  refine Finset.sum_pos' ?_ ?_
  · intro a ha
    exact hnonneg a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
  · obtain ⟨a, has, hgood, hbase⟩ := hpos
    exact ⟨a, Finset.mem_filter.mpr ⟨has, hgood⟩, hbase⟩


theorem hardFieldLimitDenominator_ne_zero_of_exists_pos {α : Type*}
    (s : Finset α) (good : α → Prop) [DecidablePred good] (base : α → ℝ)
    (hnonneg : ∀ a, a ∈ s → good a → 0 ≤ base a)
    (hpos : ∃ a, a ∈ s ∧ good a ∧ 0 < base a) :
    hardFieldLimitDenominator s good base ≠ 0 :=
  (hardFieldLimitDenominator_pos_of_exists_pos s good base hnonneg hpos).ne'






noncomputable def countHardFieldFactor {α : Type*} (penalty : α → ℕ)
    (scale H : ℝ) (a : α) : ℝ :=
  Real.exp (-(scale * H * (penalty a : ℝ)))



noncomputable def countHardFieldLimitFactor {α : Type*}
    (penalty : α → ℕ) (a : α) : ℝ :=
  if penalty a = 0 then 1 else 0



theorem countHardFieldFactor_tendsto {α : Type*}
    (penalty : α → ℕ) {scale : ℝ} (hscale : 0 < scale) (a : α) :
    Tendsto (fun H : ℝ => countHardFieldFactor penalty scale H a)
      atTop
      (𝓝 (countHardFieldLimitFactor penalty a)) := by
  by_cases hzero : penalty a = 0
  · simp [countHardFieldFactor, countHardFieldLimitFactor, hzero]
  · have hpenNat : 0 < penalty a := Nat.pos_of_ne_zero hzero
    have hpenReal : 0 < (penalty a : ℝ) := by
      exact_mod_cast hpenNat
    have hscalePenalty : 0 < scale * (penalty a : ℝ) :=
      mul_pos hscale hpenReal
    have hmul :
        Tendsto (fun H : ℝ => H * (scale * (penalty a : ℝ)))
          atTop atTop := by
      simpa using
        (Filter.Tendsto.atTop_mul_const hscalePenalty
          (Filter.tendsto_id : Tendsto (fun H : ℝ => H) atTop atTop))
    have hneg :
        Tendsto (fun H : ℝ => -(H * (scale * (penalty a : ℝ))))
          atTop atBot :=
      Filter.tendsto_neg_atTop_atBot.comp hmul
    have hexp :
        Tendsto
          (fun H : ℝ => Real.exp (-(H * (scale * (penalty a : ℝ)))))
          atTop
          (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hneg
    have hrewrite :
        (fun H : ℝ => countHardFieldFactor penalty scale H a)
          =
        (fun H : ℝ => Real.exp (-(H * (scale * (penalty a : ℝ))))) := by
      funext H
      simp [countHardFieldFactor]
      ring_nf
    simpa [countHardFieldLimitFactor, hzero, hrewrite] using hexp



theorem countHardFieldRatio_tendsto {α : Type*} (s : Finset α)
    (penalty : α → ℕ) {scale : ℝ} (hscale : 0 < scale)
    (base obs : α → ℝ)
    (hden :
      finiteFactorLimitDenominator s base
        (countHardFieldLimitFactor penalty) ≠ 0) :
    Tendsto
      (fun H : ℝ =>
        finiteFactorRatio s base obs (countHardFieldFactor penalty scale) H)
      atTop
      (𝓝
        (finiteFactorLimitRatio s base obs
          (countHardFieldLimitFactor penalty))) := by
  exact finiteFactorRatio_tendsto s base obs
    (countHardFieldLimitFactor penalty)
    (countHardFieldFactor penalty scale)
    (fun a _ha => countHardFieldFactor_tendsto penalty hscale a)
    hden




theorem countHardFieldLimitDenominator_pos_of_exists_pos {α : Type*}
    (s : Finset α) (penalty : α → ℕ) (base : α → ℝ)
    (hnonneg : ∀ a, a ∈ s → penalty a = 0 → 0 ≤ base a)
    (hpos : ∃ a, a ∈ s ∧ penalty a = 0 ∧ 0 < base a) :
    0 < finiteFactorLimitDenominator s base
      (countHardFieldLimitFactor penalty) := by
  classical
  unfold finiteFactorLimitDenominator countHardFieldLimitFactor
  refine Finset.sum_pos' ?_ ?_
  · intro a ha
    by_cases hzero : penalty a = 0
    · simpa [hzero] using hnonneg a ha hzero
    · simp [hzero]
  · obtain ⟨a, has, hzero, hbase⟩ := hpos
    refine ⟨a, has, ?_⟩
    simpa [hzero] using hbase


theorem countHardFieldLimitDenominator_ne_zero_of_exists_pos {α : Type*}
    (s : Finset α) (penalty : α → ℕ) (base : α → ℝ)
    (hnonneg : ∀ a, a ∈ s → penalty a = 0 → 0 ≤ base a)
    (hpos : ∃ a, a ∈ s ∧ penalty a = 0 ∧ 0 < base a) :
    finiteFactorLimitDenominator s base
      (countHardFieldLimitFactor penalty) ≠ 0 :=
  (countHardFieldLimitDenominator_pos_of_exists_pos
    s penalty base hnonneg hpos).ne'

end Exact3D
end StatMech
