/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.SumFreeAbelianGroups
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.Combinatorics.Additive.SumFreeAbelianGroups

open MetaMathlibExt

example {V : Type*} [Fintype V] (Γ : SimpleGraph V) [DecidableRel Γ.Adj]
    {D : ℕ} (hD : 1 ≤ D) (hV : 1 ≤ Fintype.card V) (k : ℝ)
    (htri : ∀ a b c : V, ¬(Γ.Adj a b ∧ Γ.Adj b c ∧ Γ.Adj a c))
    (hΔ : Γ.maxDegree ≤ D) (he : (Fintype.card V : ℝ) / 2 + k ≤ Γ.edgeSet.ncard) :
    (maxIndepSetCount Γ : ℝ) ≤
      (2 : ℝ) ^ ((Fintype.card V : ℝ) / 2 - k / (100 * (D : ℝ) ^ 2)) := by
  classical
  simpa using maxIndepSetCount_le_of_almost_triangleFree Γ ∅ hV hD k
    (fun a b c _ _ _ ↦ htri a b c) hΔ (by simp) (by simpa using he)

example : (maxIndepSetCount (⊥ : SimpleGraph (Fin 1)) : ℝ) ≤
    (2 : ℝ) ^ (101 / 200 : ℝ) := by
  have h := maxIndepSetCount_le_of_almost_triangleFree (⊥ : SimpleGraph (Fin 1)) ∅
    (n := 1) (D := 1) (by decide) (by decide) (-1 / 2)
    (by simp) (by simp) (by simp) (by norm_num)
  norm_num at h ⊢
  exact h

example : (maxIndepSetCount (⊥ : SimpleGraph (Fin 2)) : ℝ) ≤
    (2 : ℝ) ^ (501 / 200 : ℝ) := by
  have h := maxIndepSetCount_le_of_almost_triangleFree (⊥ : SimpleGraph (Fin 2)) {0}
    (n := 1) (D := 1) (by decide) (by decide) (-1 / 2)
    (by simp) (by simp) (by simp) (by norm_num)
  norm_num at h ⊢
  exact h

private def pentagon : SimpleGraph (Fin 5) where
  Adj a b := (a.val + 1) % 5 = b.val ∨ (b.val + 1) % 5 = a.val
  symm := ⟨fun _ _ h ↦ h.symm⟩
  loopless := ⟨by decide⟩

private instance : DecidableRel pentagon.Adj := by
  unfold pentagon
  infer_instance

example : (maxIndepSetCount pentagon : ℝ) ≤ (2 : ℝ) ^ (399 / 160 : ℝ) := by
  have he : pentagon.edgeSet.ncard = 5 := by
    rw [← pentagon.coe_edgeFinset, Set.ncard_coe_finset]
    decide
  have h := maxIndepSetCount_le_of_almost_triangleFree pentagon ∅
    (n := 5) (D := 2) (by decide) (by decide) (5 / 2)
    (by decide) (by decide) (by simp) (by simpa using he.ge)
  norm_num at h ⊢
  exact h

#check @MetaMathlibExt.maxIndepSetCount_le_of_almost_triangleFree
#print axioms MetaMathlibExt.maxIndepSetCount_le_of_almost_triangleFree

end MathlibExtTest.Combinatorics.Additive.SumFreeAbelianGroups
