/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.RamseyWitnessTensorSquare
import Mathlib.Order.Interval.Finset.Basic

/-! # Tests for Ramsey's witnesses and tensor squares of ultrafilters -/

open Filter

namespace MetaMathlibExt.ramseyWitness_iff_mem_closure_tensor_squares

-- The tensor square of `hyperfilter ℕ` is a Ramsey's witness.
example (X : Set (ℕ × ℕ))
    (hX : X ∈ (hyperfilter ℕ).bind fun n => (hyperfilter ℕ).map (Prod.mk n)) :
    ∃ H : Set ℕ, H.Infinite ∧ ∀ h ∈ H, ∀ h' ∈ H, h < h' → (h, h') ∈ X :=
  (ramseyWitness_iff_mem_closure_tensor_squares _).2
    (subset_closure ⟨hyperfilter ℕ, hyperfilter_le_cofinite, rfl⟩) X hX

-- Ramsey's theorem for pairs in two colours: every `X ⊆ ℕ × ℕ` or its complement contains `[H]²`
-- for an infinite `H`, because one of them lies in a Ramsey's witness.
example (X : Set (ℕ × ℕ)) : ∃ H : Set ℕ, H.Infinite ∧
    ((∀ h ∈ H, ∀ h' ∈ H, h < h' → (h, h') ∈ X) ∨
      ∀ h ∈ H, ∀ h' ∈ H, h < h' → (h, h') ∉ X) := by
  set W : Ultrafilter (ℕ × ℕ) := (hyperfilter ℕ).bind fun n => (hyperfilter ℕ).map (Prod.mk n)
  have hW := (ramseyWitness_iff_mem_closure_tensor_squares W).2
    (subset_closure ⟨hyperfilter ℕ, hyperfilter_le_cofinite, rfl⟩)
  rcases W.mem_or_compl_mem X with hX | hX
  · obtain ⟨H, hH, hHX⟩ := hW X hX
    exact ⟨H, hH, Or.inl hHX⟩
  · obtain ⟨H, hH, hHX⟩ := hW Xᶜ hX
    exact ⟨H, hH, Or.inr hHX⟩

-- Every point of the closure contains the strict upper triangle `{(a, b) | a < b}`, so for
-- instance no ultrafilter concentrated on the diagonal lies in it.
example (W : Ultrafilter (ℕ × ℕ))
    (hW : W ∈ closure {V : Ultrafilter (ℕ × ℕ) | ∃ U : Ultrafilter ℕ,
      (U : Filter ℕ) ≤ cofinite ∧ V = U.bind fun n => U.map (Prod.mk n)}) :
    {p : ℕ × ℕ | p.1 < p.2} ∈ W := by
  by_contra hlt
  obtain ⟨H, hH, hHX⟩ := (ramseyWitness_iff_mem_closure_tensor_squares W).2 hW _
    (W.compl_mem_iff_notMem.2 hlt)
  obtain ⟨a, ha, -⟩ := hH.exists_gt 0
  obtain ⟨b, hb, hab⟩ := hH.exists_gt a
  exact hHX a ha b hb hab hab

-- A principal ultrafilter is not in the closure, even when it contains the upper triangle.
example :
    (pure (0, 1) : Ultrafilter (ℕ × ℕ)) ∉ closure {V : Ultrafilter (ℕ × ℕ) | ∃ U : Ultrafilter ℕ,
      (U : Filter ℕ) ≤ cofinite ∧ V = U.bind fun n => U.map (Prod.mk n)} := by
  intro h
  obtain ⟨H, hH, hHX⟩ :=
    (ramseyWitness_iff_mem_closure_tensor_squares (pure (0, 1))).2 h {(0, 1)} rfl
  obtain ⟨a, ha, ha0⟩ := hH.exists_gt 0
  obtain ⟨b, hb, hab⟩ := hH.exists_gt a
  have hpair : (a, b) = (0, 1) := hHX a ha b hb hab
  simp only [Prod.mk.injEq] at hpair
  omega

end MetaMathlibExt.ramseyWitness_iff_mem_closure_tensor_squares
