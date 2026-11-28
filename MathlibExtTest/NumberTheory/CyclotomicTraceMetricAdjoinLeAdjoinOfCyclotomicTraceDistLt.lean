/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CyclotomicTraceMetricAdjoinLeAdjoinOfCyclotomicTraceDistLt
import MathlibExt.NumberTheory.CyclotomicTraceMetric
import Mathlib.Tactic.Linarith

/-! # Tests for the Krasner-type lemma for the cyclotomic trace metric -/

namespace MathlibExtTest.NumberTheory.CyclotomicTraceMetricAdjoinLeAdjoinOfCyclotomicTraceDistLt

open MetaMathlibExt

variable {p : ℕ} [NeZero p] {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K]

-- At distance zero the Krasner hypothesis holds, so the lemma recovers reflexivity.
example (hp : p.Prime) (α : K) :
    IntermediateField.adjoin ℚ {α} ≤ IntermediateField.adjoin ℚ {α} := by
  apply adjoin_le_adjoin_of_cyclotomicTraceDist_lt hp
  intro σ hσ
  rw [cyclotomicTraceDist_self]
  have hsub : α - σ α ≠ 0 := sub_ne_zero.mpr hσ.symm
  have hne : cyclotomicTraceDist p α (σ α) ≠ 0 := by
    have hnorm : cyclotomicTraceNorm p (α - σ α) ≠ 0 :=
      ((cyclotomicTraceNorm_isNorm (K := K) hp).1 _).not.mpr hsub
    simpa [cyclotomicTraceDist] using hnorm
  have hnn : 0 ≤ cyclotomicTraceDist p α (σ α) := by
    rw [cyclotomicTraceDist, cyclotomicTraceNorm]
    exact Real.sqrt_nonneg _
  have hpos : 0 < cyclotomicTraceDist p α (σ α) := lt_of_le_of_ne hnn hne.symm
  linarith

-- The lemma says `α` itself lies in `ℚ(β)`.
example (hp : p.Prime) {α β : K}
    (h : ∀ σ : K ≃ₐ[ℚ] K, σ α ≠ α →
      cyclotomicTraceDist p α β < cyclotomicTraceDist p α (σ α) / 2) :
    α ∈ IntermediateField.adjoin ℚ {β} :=
  adjoin_le_adjoin_of_cyclotomicTraceDist_lt hp h
    (IntermediateField.subset_adjoin ℚ {α} (by simp))

-- Closeness both ways identifies the two generated subfields.
example (hp : p.Prime) {α β : K}
    (hα : ∀ σ : K ≃ₐ[ℚ] K, σ α ≠ α →
      cyclotomicTraceDist p α β < cyclotomicTraceDist p α (σ α) / 2)
    (hβ : ∀ σ : K ≃ₐ[ℚ] K, σ β ≠ β →
      cyclotomicTraceDist p β α < cyclotomicTraceDist p β (σ β) / 2) :
    IntermediateField.adjoin ℚ {α} = IntermediateField.adjoin ℚ {β} :=
  le_antisymm (adjoin_le_adjoin_of_cyclotomicTraceDist_lt hp hα)
    (adjoin_le_adjoin_of_cyclotomicTraceDist_lt hp hβ)

end MathlibExtTest.NumberTheory.CyclotomicTraceMetricAdjoinLeAdjoinOfCyclotomicTraceDistLt
