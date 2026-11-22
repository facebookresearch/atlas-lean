/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCofaceVertices

/-!
# The entire original root cube splits at its original coface coordinate

The exact original coface preimage and the actual membership coordinate
read the whole original subset. Reconstruction inserts that same omitted
coordinate precisely in the original upper interval layer. Both complete
subset inverses and monotonicity give the original whole root-cube order
isomorphism. No product-marking or weak-class assertion is assumed.
-/

noncomputable section
universe u
open CategoryTheory

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The original interval coordinate records exactly membership of the same original larger-root ordinal vertex. -/
def coneRootCoordinateMembership {n : ℕ} (j : Fin (n + 2))
    (a : ConeSubset (⊥ : Vertex.{u} (n + 1))) : Vertex.{u} 1 :=
  if ULift.up j ∈ a.vertices then ⊤ else ⊥

/-- Inclusion of complete original subsets is monotone in the unchanged original membership interval coordinate. -/
theorem coneRootCoordinateMembership_mono {n : ℕ} (j : Fin (n + 2)) :
    Monotone (coneRootCoordinateMembership.{u} j) := by
  intro a b h
  by_cases ha : ULift.up j ∈ a.vertices
  · have hb : ULift.up j ∈ b.vertices := h ha
    simp only [coneRootCoordinateMembership, ite_eq_left ha, ite_eq_left hb]
    exact le_rfl
  · by_cases hb : ULift.up j ∈ b.vertices
    · simp only [coneRootCoordinateMembership, ite_eq_right ha, ite_eq_left hb]
      exact bot_le
    · simp only [coneRootCoordinateMembership, ite_eq_right ha, ite_eq_right hb]
      exact le_rfl

/-- The whole actual original root coface image excludes precisely its omitted original coordinate. -/
theorem coneRootCofaceSubset_not_mem {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : ConeSubset (⊥ : Vertex.{u} n)) : ULift.up j ∉ (coneRootCofaceSubset j hj a).vertices := by
  intro h
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
  have hne : coneCofaceEmbedding j k ≠ ULift.up j :=
    (mem_coneCofaceEmbedding_range j _).mp ⟨k, rfl⟩
  exact hne hk

/-- The same original coface preimage is unchanged by inserting precisely the one omitted original coordinate. -/
theorem coneRootCofacePreimage_insert {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : ConeSubset (⊥ : Vertex.{u} (n + 1))) :
    coneRootCofacePreimage j hj (coneRootInsert (ULift.up j) a) = coneRootCofacePreimage j hj a := by
  apply ConeSubset.ext
  ext k
  have hne : coneCofaceEmbedding j k ≠ ULift.up j :=
    (mem_coneCofaceEmbedding_range j _).mp ⟨k, rfl⟩
  simp only [coneRootCofacePreimage, coneRootInsert, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_insert, hne, false_or]

/-- Rebuild the whole original larger-root subset from its exact original membership interval and complete original
coface preimage. -/
def coneRootCoordinateRebuild {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (z : Vertex.{u} 1 × ConeSubset (⊥ : Vertex.{u} n)) : ConeSubset (⊥ : Vertex.{u} (n + 1)) :=
  coneRootCoordinateLevel (ULift.up j) (z.1, coneRootCofaceSubset j hj z.2)

/-- The original whole subset reconstruction is monotone in both unchanged original coordinates. -/
theorem coneRootCoordinateRebuild_mono {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    Monotone (coneRootCoordinateRebuild.{u} j hj) :=
  fun _ _ h => coneRootCoordinateLevel_mono (ULift.up j)
    ⟨h.1, coneRootCofaceSubset_mono j hj h.2⟩

/-- Read the actual original membership coordinate and the same complete original finite coface preimage. -/
def coneRootCoordinateSplit {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : ConeSubset (⊥ : Vertex.{u} (n + 1))) : Vertex.{u} 1 × ConeSubset (⊥ : Vertex.{u} n) :=
  (coneRootCoordinateMembership j a, coneRootCofacePreimage j hj a)

/-- The whole original coordinate reader keeps the unchanged inclusion order on both of its actual coordinates. -/
theorem coneRootCoordinateSplit_mono {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    Monotone (coneRootCoordinateSplit.{u} j hj) :=
  fun _ _ h => ⟨coneRootCoordinateMembership_mono j h, coneRootCofacePreimage_mono j hj h⟩

private theorem originalInterval_top_ne_bot : (⊤ : Vertex.{u} 1) ≠ ⊥ := by decide

/-- Reconstructing the same original coface preimage and membership coordinate recovers every original larger-root
subset and all its original vertices. -/
theorem coneRootCoordinateRebuild_split {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : ConeSubset (⊥ : Vertex.{u} (n + 1))) :
    coneRootCoordinateRebuild j hj (coneRootCoordinateSplit j hj a) = a := by
  by_cases ha : ULift.up j ∈ a.vertices
  · simp only [coneRootCoordinateSplit, coneRootCoordinateRebuild, coneRootCoordinateMembership,
      ite_eq_left ha, coneRootCoordinateLevel, ite_eq_right originalInterval_top_ne_bot]
    apply ConeSubset.ext
    change insert (ULift.up j) (coneRootCofaceSubset j hj (coneRootCofacePreimage j hj a)).vertices = a.vertices
    rw [coneRootCofaceImage_preimage_vertices, Finset.insert_erase ha]
  · simp only [coneRootCoordinateSplit, coneRootCoordinateRebuild, coneRootCoordinateMembership,
      ite_eq_right ha, coneRootCoordinateLevel, ite_true]
    apply ConeSubset.ext
    exact (coneRootCofaceImage_preimage_vertices j hj a).trans (Finset.erase_eq_of_notMem ha)

/-- Reading either entire original interval layer after reconstruction recovers the same actual interval value and
full original smaller-root subset. -/
theorem coneRootCoordinateSplit_rebuild {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (z : Vertex.{u} 1 × ConeSubset (⊥ : Vertex.{u} n)) :
    coneRootCoordinateSplit j hj (coneRootCoordinateRebuild j hj z) = z := by
  rcases z with ⟨⟨t⟩, a⟩
  fin_cases t
  · change (coneRootCoordinateMembership j (coneRootCoordinateLevel (ULift.up j)
        (⊥, coneRootCofaceSubset j hj a)), coneRootCofacePreimage j hj
        (coneRootCoordinateLevel (ULift.up j) (⊥, coneRootCofaceSubset j hj a))) = (⊥, a)
    simp only [coneRootCoordinateLevel, ite_true]
    apply Prod.ext
    · simp only [coneRootCoordinateMembership, ite_eq_right (coneRootCofaceSubset_not_mem j hj a)]
    · exact coneRootCofacePreimage_image j hj a
  · change (coneRootCoordinateMembership j (coneRootCoordinateLevel (ULift.up j)
        (⊤, coneRootCofaceSubset j hj a)), coneRootCofacePreimage j hj
        (coneRootCoordinateLevel (ULift.up j) (⊤, coneRootCofaceSubset j hj a))) = (⊤, a)
    simp only [coneRootCoordinateLevel, ite_eq_right originalInterval_top_ne_bot]
    apply Prod.ext
    · simp only [coneRootCoordinateMembership, coneRootInsert, Finset.mem_insert_self, ite_true]
    · exact (coneRootCofacePreimage_insert j hj (coneRootCofaceSubset j hj a)).trans
        (coneRootCofacePreimage_image j hj a)

/-- The entire original larger-root cube is order-isomorphic to the unchanged original membership interval and
complete smaller-root cube, with both original subset inverses proved. -/
def coneRootCoordinateOrderIso {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    ConeSubset (⊥ : Vertex.{u} (n + 1)) ≃o Vertex.{u} 1 × ConeSubset (⊥ : Vertex.{u} n) :=
  Equiv.toOrderIso
    { toFun := coneRootCoordinateSplit j hj
      invFun := coneRootCoordinateRebuild j hj
      left_inv := coneRootCoordinateRebuild_split j hj
      right_inv := coneRootCoordinateSplit_rebuild j hj }
    (coneRootCoordinateSplit_mono j hj) (coneRootCoordinateRebuild_mono j hj)

end SSet.Marked.CoherentWeight
