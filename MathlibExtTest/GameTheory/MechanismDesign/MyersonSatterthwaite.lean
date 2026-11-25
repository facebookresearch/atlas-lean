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

/- When the intervals only touch, a fixed price at their common endpoint works. Trading at
price zero gives every seller in [-1,0] and every buyer in [0,1] a nonnegative utility.
Allocation and payment are constant, so reports cannot affect either utility. -/
example (s v : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) (hv : v ∈ Icc (0 : ℝ) 1) :
    s ≤ v ∧ (0 ≤ ∫ _ in (0 : ℝ)..1, (0 - s * 1)) ∧
      (0 ≤ ∫ _ in (-1 : ℝ)..0, (v * 1 - 0)) := by
  simpa using And.intro (hs.2.trans hv.1) (And.intro hs.2 hv.1)

end MathlibExtTest.GameTheory.MyersonSatterthwaite
