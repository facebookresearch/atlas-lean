/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceComplex
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalTwoBeadInnerAnodyne
import Mathlib.Data.Finset.Max

/-!
# The actual first crossed joint of a missing original necklace simplex

The original support and joint set define every crossing. Adding the
selected joint preserves precisely the same crossed joints; removing
it from a crossing simplex does likewise. All original vertices and
full standard simplices remain the canonical native ones.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace.CrossedJoints

/-- The actual original joints crossed by the entire supplied support. -/
def crossed {n : ℕ} (J I : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) := by
  classical
  exact J.filter (fun k => (∃ a ∈ I, a < k) ∧ ∃ b ∈ I, k < b)

/-- Original membership is exactly the two original strict-side support tests. -/
theorem mem_crossed {n : ℕ} (J I : Finset (Fin (n + 1))) (k : Fin (n + 1)) :
    k ∈ crossed J I ↔ k ∈ J ∧ (∃ a ∈ I, a < k) ∧ ∃ b ∈ I, k < b := by
  classical
  simp only [crossed, Finset.mem_filter]

/-- Adding an original pivot already strictly between support vertices preserves all actual crossed joints. -/
theorem crossed_insert {n : ℕ} (J I : Finset (Fin (n + 1))) (k : Fin (n + 1))
    (hk : (∃ a ∈ I, a < k) ∧ ∃ b ∈ I, k < b) :
    crossed J (insert k I) = crossed J I := by
  classical
  ext j
  rw [mem_crossed, mem_crossed]
  constructor
  · rintro ⟨hj, ⟨a, ha, haj⟩, b, hb, hjb⟩
    refine ⟨hj, ?_, ?_⟩
    · rcases Finset.mem_insert.mp ha with rfl | ha
      · obtain ⟨a, ha, hak⟩ := hk.1
        exact ⟨a, ha, hak.trans haj⟩
      · exact ⟨a, ha, haj⟩
    · rcases Finset.mem_insert.mp hb with rfl | hb
      · obtain ⟨b, hb, hkb⟩ := hk.2
        exact ⟨b, hb, hjb.trans hkb⟩
      · exact ⟨b, hb, hjb⟩
  · rintro ⟨hj, ⟨a, ha, haj⟩, b, hb, hjb⟩
    exact ⟨hj, ⟨a, Finset.mem_insert_of_mem ha, haj⟩, b, Finset.mem_insert_of_mem hb, hjb⟩

/-- Deleting an actually crossed original pivot preserves all actual crossed joints. -/
theorem crossed_erase {n : ℕ} (J I : Finset (Fin (n + 1))) (k : Fin (n + 1))
    (hk : k ∈ crossed J I) : crossed J (I.erase k) = crossed J I := by
  classical
  obtain ⟨_, ⟨a, ha, hak⟩, b, hb, hkb⟩ := (mem_crossed J I k).mp hk
  have hac : a ∈ I.erase k := Finset.mem_erase.mpr ⟨ne_of_lt hak, ha⟩
  have hbc : b ∈ I.erase k := Finset.mem_erase.mpr ⟨ne_of_gt hkb, hb⟩
  by_cases hki : k ∈ I
  · have h := crossed_insert J (I.erase k) k ⟨⟨a, hac, hak⟩, b, hbc, hkb⟩
    rw [Finset.insert_erase hki] at h
    exact h.symm
  · rw [Finset.erase_eq_of_notMem hki]

/-- Missing original nondegenerate simplices have a genuinely nonempty set of crossed original joints. -/
theorem crossed_nonempty {n d : ℕ} (J : Finset (Fin (n + 1)))
    (x : (Δ[n] : SSet.{u}).nonDegenerate d)
    (hx : x.val ∉ (complex J).obj (op ⦋d⦌)) :
    (crossed J (stdSimplex.nonDegenerateEquiv' x).val).Nonempty := by
  classical
  have h : ¬ ∀ k ∈ J, x.val ∈ (OriginalTwoBead.union k).obj (op ⦋d⦌) := by
    intro h
    apply hx
    exact (mem_complex_iff J x.val).mpr (fun k hk => (OriginalTwoBead.mem_union_iff k x.val).mp (h k hk))
  obtain ⟨k, hmissing⟩ := not_forall.mp h
  have hmissing := not_imp.mp hmissing
  obtain ⟨⟨a, ha⟩, b, hb⟩ := (OriginalTwoBead.not_mem_union_iff k x.val).mp hmissing.2
  refine ⟨k, (mem_crossed _ _ _).mpr ⟨hmissing.1, ?_, ?_⟩⟩
  · exact ⟨x.val a, (stdSimplex.nonDegenerateEquiv'_iff _ _).mpr ⟨a, rfl⟩, ha⟩
  · exact ⟨x.val b, (stdSimplex.nonDegenerateEquiv'_iff _ _).mpr ⟨b, rfl⟩, hb⟩

end SSet.OriginalNecklace.CrossedJoints
