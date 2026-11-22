/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceBeadIntervals

/-!
# Actual whole original necklace cuts at a supplied joint

The prefix and suffix retain precisely the original joint preimages
under the SAME complete native interval operators. Every original
simplex and both cut endpoints are retained, including cuts at either
original endpoint.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace.Cut

open CategoryTheory.CoherentRealization.OriginalBeadInterval

/-- The SAME full original prefix embedding at an actual original vertex. -/
abbrev leftEmbedding (T : Data) (j : Fin (T.dimension + 1)) :
    Fin (length 0 j + 1) ↪o Fin (T.dimension + 1) :=
  embedding 0 j (Fin.zero_le j)

/-- The SAME full original suffix embedding at that original vertex. -/
abbrev rightEmbedding (T : Data) (j : Fin (T.dimension + 1)) :
    Fin (length j (Fin.last T.dimension) + 1) ↪o Fin (T.dimension + 1) :=
  embedding j (Fin.last T.dimension) (Fin.le_last j)

/-- The actual full prefix joint set is precisely the original joint preimage. -/
def leftJoints (T : Data) (j : Fin (T.dimension + 1)) : Finset (Fin (length 0 j + 1)) := by
  classical
  exact Finset.univ.filter (fun i => leftEmbedding T j i ∈ T.joints)

/-- The actual full suffix joint set is precisely the original joint preimage. -/
def rightJoints (T : Data) (j : Fin (T.dimension + 1)) :
    Finset (Fin (length j (Fin.last T.dimension) + 1)) := by
  classical
  exact Finset.univ.filter (fun i => rightEmbedding T j i ∈ T.joints)

/-- Prefix membership is exactly its SAME original mapped joint membership. -/
theorem mem_leftJoints (T : Data) (j : Fin (T.dimension + 1)) (i : Fin (length 0 j + 1)) :
    i ∈ leftJoints T j ↔ leftEmbedding T j i ∈ T.joints := by
  classical
  simp only [leftJoints, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Suffix membership is exactly its SAME original mapped joint membership. -/
theorem mem_rightJoints (T : Data) (j : Fin (T.dimension + 1))
    (i : Fin (length j (Fin.last T.dimension) + 1)) :
    i ∈ rightJoints T j ↔ rightEmbedding T j i ∈ T.joints := by
  classical
  simp only [rightJoints, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The whole original prefix necklace at an actual original joint. -/
abbrev leftData (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) : Data where
  dimension := length 0 j
  joints := leftJoints T j
  source_joint := (mem_leftJoints T j 0).mpr (by rw [embedding_zero]; exact T.source_joint)
  target_joint := (mem_leftJoints T j _).mpr (by rw [embedding_last]; exact hj)

/-- The whole original suffix necklace at that SAME original joint. -/
abbrev rightData (T : Data) (j : Fin (T.dimension + 1)) (hj : j ∈ T.joints) : Data where
  dimension := length j (Fin.last T.dimension)
  joints := rightJoints T j
  source_joint := (mem_rightJoints T j 0).mpr (by rw [embedding_zero]; exact hj)
  target_joint := (mem_rightJoints T j _).mpr (by rw [embedding_last]; exact T.target_joint)

/-- Every whole original prefix simplex has its exact original necklace membership. -/
theorem left_mem_iff (T : Data) (j : Fin (T.dimension + 1)) {d : ℕ}
    (s : (Δ[length 0 j] : SSet.{u}) _⦋d⦌) :
    (SSet.stdSimplex.map (operator 0 j (Fin.zero_le j))).app (op ⦋d⦌) s ∈
      (complex T.joints).obj (op ⦋d⦌) ↔ s ∈ (complex (leftJoints T j)).obj (op ⦋d⦌) := by
  constructor
  · intro hs
    apply (mem_complex_iff _ _).mpr
    intro i hi
    have h := (mem_complex_iff _ _).mp hs (leftEmbedding T j i) ((mem_leftJoints T j i).mp hi)
    rcases h with h | h
    · exact Or.inl (fun k => (leftEmbedding T j).le_iff_le.mp (h k))
    · exact Or.inr (fun k => (leftEmbedding T j).le_iff_le.mp (h k))
  · intro hs
    apply (mem_complex_iff _ _).mpr
    intro i hi
    by_cases hij : i ≤ j
    · obtain ⟨k, hk⟩ := coverage 0 j (Fin.zero_le j) (ULift.up.{u} i)
        (by rw [lifted_zero]; exact Fin.zero_le _) (by rw [lifted_last]; exact hij)
      have hk' : leftEmbedding T j k.down = i := congrArg ULift.down hk
      have hjk := (mem_leftJoints T j k.down).mpr (hk'.symm ▸ hi)
      rcases (mem_complex_iff _ _).mp hs k.down hjk with h | h
      · exact Or.inl (fun r => ((leftEmbedding T j).monotone (h r)).trans hk'.le)
      · exact Or.inr (fun r => hk'.symm.le.trans ((leftEmbedding T j).monotone (h r)))
    · apply Or.inl
      intro r
      have h := (leftEmbedding T j).monotone (Fin.le_last (s r))
      rw [embedding_last] at h
      exact h.trans (not_le.mp hij).le

/-- Every whole original suffix simplex has its exact original necklace membership. -/
theorem right_mem_iff (T : Data) (j : Fin (T.dimension + 1)) {d : ℕ}
    (s : (Δ[length j (Fin.last T.dimension)] : SSet.{u}) _⦋d⦌) :
    (SSet.stdSimplex.map (operator j (Fin.last T.dimension) (Fin.le_last j))).app (op ⦋d⦌) s ∈
      (complex T.joints).obj (op ⦋d⦌) ↔ s ∈ (complex (rightJoints T j)).obj (op ⦋d⦌) := by
  constructor
  · intro hs
    apply (mem_complex_iff _ _).mpr
    intro i hi
    have h := (mem_complex_iff _ _).mp hs (rightEmbedding T j i) ((mem_rightJoints T j i).mp hi)
    rcases h with h | h
    · exact Or.inl (fun k => (rightEmbedding T j).le_iff_le.mp (h k))
    · exact Or.inr (fun k => (rightEmbedding T j).le_iff_le.mp (h k))
  · intro hs
    apply (mem_complex_iff _ _).mpr
    intro i hi
    by_cases hji : j ≤ i
    · obtain ⟨k, hk⟩ := coverage j (Fin.last T.dimension) (Fin.le_last j) (ULift.up.{u} i)
        (by rw [lifted_zero]; exact hji) (by rw [lifted_last]; exact Fin.le_last _)
      have hk' : rightEmbedding T j k.down = i := congrArg ULift.down hk
      have hjk := (mem_rightJoints T j k.down).mpr (hk'.symm ▸ hi)
      rcases (mem_complex_iff _ _).mp hs k.down hjk with h | h
      · exact Or.inl (fun r => ((rightEmbedding T j).monotone (h r)).trans hk'.le)
      · exact Or.inr (fun r => hk'.symm.le.trans ((rightEmbedding T j).monotone (h r)))
    · apply Or.inr
      intro r
      have h := (rightEmbedding T j).monotone (Fin.zero_le (s r))
      rw [embedding_zero] at h
      exact (not_le.mp hji).le.trans h

end SSet.OriginalNecklace.Cut
