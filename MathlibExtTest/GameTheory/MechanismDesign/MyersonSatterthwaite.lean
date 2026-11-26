/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.MechanismDesign.MyersonSatterthwaite
import Mathlib.Tactic.NormNum

open Set MeasureTheory MathlibExt.GameTheory.MyersonSatterthwaiteWanted

namespace MathlibExtTest.GameTheory.MyersonSatterthwaite

private noncomputable def trade (s v : ℝ) : ℝ := if s < v then 1 else 0

/- On two uniform unit intervals, every incentive-compatible payment for the strict
trading rule gives at least one type negative interim utility. -/
example (x : ℝ → ℝ → ℝ)
    (hx : IntegrableOn x.uncurry (Icc 0 1 ×ˢ Icc 0 1))
    (hs : ∀ s ∈ Icc (0 : ℝ) 1, IntervalIntegrable (x s) volume 0 1)
    (hb : ∀ v ∈ Icc (0 : ℝ) 1, IntervalIntegrable (fun s => x s v) volume 0 1)
    (hicS : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ v in (0 : ℝ)..1, x t v - s * trade t v) ≤ ∫ v in (0 : ℝ)..1, x s v - s * trade s v)
    (hicB : ∀ v ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (0 : ℝ) 1,
      (∫ s in (0 : ℝ)..1, v * trade s w - x s w) ≤ ∫ s in (0 : ℝ)..1, v * trade s v - x s v) :
    (∃ s ∈ Icc (0 : ℝ) 1, (∫ v in (0 : ℝ)..1, x s v - s * trade s v) < 0) ∨
      ∃ v ∈ Icc (0 : ℝ) 1, (∫ s in (0 : ℝ)..1, v * trade s v - x s v) < 0 := by
  by_contra! hir
  apply myerson_satterthwaite zero_lt_one zero_lt_one zero_lt_one zero_lt_one
    (f₁ := fun _ => 1) (f₂ := fun _ => 1) continuousOn_const continuousOn_const
    (fun _ _ => zero_lt_one) (fun _ _ => zero_lt_one) (by norm_num) (by norm_num) trade x
    _ _ hx hs hb
  · simpa using hicS
  · simpa using hicB
  · simpa using hir.1
  · simpa using hir.2
  · intro s _ v _
    exact ⟨fun h => by simp [trade, h], fun h => by simp [trade, h.not_gt]⟩
  · exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      measurable_const measurable_const
  · intro s _ v _
    unfold trade
    split <;> norm_num

/- The overlap hypothesis `a₂ < b₁` cannot be dropped. When the intervals `[-1, 0]` and `[0, 1]`
only touch, uniform densities with the mechanism "always trade at price zero" (`p = 1`, `x = 0`)
satisfy every other hypothesis of `myerson_satterthwaite`: reports affect neither utility, every
seller value is at most every buyer value, and both interim utilities are nonnegative. -/
example : ¬ ∀ (a₁ b₁ a₂ b₂ : ℝ) (f₁ f₂ : ℝ → ℝ) (p x : ℝ → ℝ → ℝ),
    a₁ < b₁ → a₂ < b₂ → a₁ < b₂ →
    ContinuousOn f₁ (Icc a₁ b₁) → ContinuousOn f₂ (Icc a₂ b₂) →
    (∀ v ∈ Icc a₁ b₁, 0 < f₁ v) → (∀ v ∈ Icc a₂ b₂, 0 < f₂ v) →
    ∫ v in a₁..b₁, f₁ v = 1 → ∫ v in a₂..b₂, f₂ v = 1 →
    Measurable (Function.uncurry p) →
    (∀ v₁ ∈ Icc a₁ b₁, ∀ v₂ ∈ Icc a₂ b₂, p v₁ v₂ ∈ Icc (0 : ℝ) 1) →
    IntegrableOn (Function.uncurry x) (Icc a₁ b₁ ×ˢ Icc a₂ b₂) →
    (∀ v₁ ∈ Icc a₁ b₁, IntervalIntegrable (x v₁) volume a₂ b₂) →
    (∀ v₂ ∈ Icc a₂ b₂, IntervalIntegrable (fun v₁ => x v₁ v₂) volume a₁ b₁) →
    (∀ v₁ ∈ Icc a₁ b₁, ∀ w₁ ∈ Icc a₁ b₁,
      ∫ v₂ in a₂..b₂, (x w₁ v₂ - v₁ * p w₁ v₂) * f₂ v₂ ≤
        ∫ v₂ in a₂..b₂, (x v₁ v₂ - v₁ * p v₁ v₂) * f₂ v₂) →
    (∀ v₂ ∈ Icc a₂ b₂, ∀ w₂ ∈ Icc a₂ b₂,
      ∫ v₁ in a₁..b₁, (v₂ * p v₁ w₂ - x v₁ w₂) * f₁ v₁ ≤
        ∫ v₁ in a₁..b₁, (v₂ * p v₁ v₂ - x v₁ v₂) * f₁ v₁) →
    (∀ v₁ ∈ Icc a₁ b₁, 0 ≤ ∫ v₂ in a₂..b₂, (x v₁ v₂ - v₁ * p v₁ v₂) * f₂ v₂) →
    (∀ v₂ ∈ Icc a₂ b₂, 0 ≤ ∫ v₁ in a₁..b₁, (v₂ * p v₁ v₂ - x v₁ v₂) * f₁ v₁) →
    (∀ v₁ ∈ Icc a₁ b₁, ∀ v₂ ∈ Icc a₂ b₂,
      (v₁ < v₂ → p v₁ v₂ = 1) ∧ (v₂ < v₁ → p v₁ v₂ = 0)) →
    False := by
  intro h
  refine h (-1) 0 0 1 (fun _ => 1) (fun _ => 1) (fun _ _ => 1) (fun _ _ => 0)
    (by norm_num) (by norm_num) (by norm_num) continuousOn_const continuousOn_const
    (fun _ _ => one_pos) (fun _ _ => one_pos) (by norm_num) (by norm_num) measurable_const
    (fun _ _ _ _ => ⟨zero_le_one, le_rfl⟩) integrableOn_zero
    (fun _ _ => intervalIntegrable_const) (fun _ _ => intervalIntegrable_const)
    (fun _ _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl) (fun v hv => ?_) (fun v hv => ?_)
    (fun s hs v hv => ⟨fun _ => rfl, fun hvs => absurd hvs (not_lt.mpr (hs.2.trans hv.1))⟩)
  · norm_num
    exact hv.2
  · norm_num
    exact hv.1

end MathlibExtTest.GameTheory.MyersonSatterthwaite
