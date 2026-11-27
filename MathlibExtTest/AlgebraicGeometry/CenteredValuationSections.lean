/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CenteredValuationSections

/-! # Filtration sign and faithful-value regression checks -/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.BirationalSectionCoordinates
open MathlibExt.AlgebraicGeometry.CenteredValuationSections

namespace MathlibExtTest.AlgebraicGeometry.CenteredValuationSections

variable {k : Type} [Field k] {n : ℕ} (V : NormalVariety k n)
  (v : CenteredValuation V) (M : V.X.left.Modules) (E : Evaluation V v.center M)

/-- Actual local section values ensure the whole section space lies in every nonpositive step. -/
example (t : ℝ) (ht : t ≤ 0) : filteredSpace v M E t = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro s
  change v.valuation (E.map s) ≤ Real.toNNReal (Real.exp (-t))
  rw [E.normalized]
  apply (v.bounded (localValue E.frame s)).trans
  apply (NNReal.coe_le_coe).mp
  rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
  exact (Real.one_le_exp_iff).mpr (neg_nonneg.mpr ht)

/-- A trivial metric and an injective actual germ map leave only zero in a positive step.
This catches the opposite exponential sign and unfaithful section-value carriers. -/
example (t : ℝ) (ht : 0 < t)
    (htrivial : ∀ a : FunctionField V, a ≠ 0 → v.valuation a = 1) :
    filteredSpace v M E t = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro s hs
  rw [Submodule.mem_bot]
  by_contra h
  have hE : E.map s ≠ 0 := by
    intro he
    apply h
    apply E.injective
    simpa only [map_zero] using he
  change v.valuation (E.map s) ≤ Real.toNNReal (Real.exp (-t)) at hs
  rw [htrivial _ hE] at hs
  have hlt : Real.toNNReal (Real.exp (-t)) < 1 := by
    apply (NNReal.coe_lt_coe).mp
    rw [Real.coe_toNNReal _ (Real.exp_pos _).le]
    exact (Real.exp_lt_one_iff).mpr (neg_neg_of_pos ht)
  exact (not_lt_of_ge hs) hlt

end MathlibExtTest.AlgebraicGeometry.CenteredValuationSections
