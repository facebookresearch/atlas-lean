/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeFiltration

/-!
# The whole original bounded cone is its preceding-stage cylinder

For a least vertex strictly below the new maximum, deleting that maximum
and recording whether it was present gives an order isomorphism with
the preceding stage times the original two-vertex interval. The inverse
inserts precisely that vertex in the top layer. All original subsets
and inclusions are retained.
-/

noncomputable section
universe u
open CategoryTheory

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The actual interval coordinate records only whether the original subset has reached the new maximum. -/
def coneFiltrationLevel {n : ℕ} {i k : Vertex.{u} n} (a : ConeAtMost i k) : Vertex.{u} 1 :=
  if a.val.maximum = k then ULift.up 1 else ULift.up 0

/-- Original inclusion cannot return from the top maximum to the preceding stage. -/
theorem coneFiltrationLevel_mono {n : ℕ} {i k : Vertex.{u} n} :
    Monotone (@coneFiltrationLevel _ i k) := by
  intro a b hab
  by_cases ha : a.val.maximum = k
  · have hb : b.val.maximum = k := le_antisymm b.property
      (ha.symm.le.trans (ConeSubset.maximum_mono hab))
    simp only [coneFiltrationLevel, ite_eq_left ha, ite_eq_left hb, le_refl]
  · by_cases hb : b.val.maximum = k <;>
      simp [coneFiltrationLevel, ha, hb]

/-- Recover a whole original subset by inserting the new vertex exactly at the actual top interval coordinate. -/
def coneFromFiltration {n : ℕ} {i k : Vertex.{u} n} (hi : i < k)
    (a : ConeBefore i k × Vertex.{u} 1) : ConeAtMost i k :=
  if a.2.down = 0 then ⟨a.1.val, a.1.property.le⟩
  else ⟨(coneInsertTop hi a.1).val, (coneInsertTop hi a.1).property.le⟩

/-- Reconstructing from the erased subset and its original top coordinate recovers every original vertex. -/
theorem coneFromFiltration_erase {n : ℕ} {i k : Vertex.{u} n} (hi : i < k)
    (a : ConeAtMost i k) :
    coneFromFiltration hi (coneEraseTop hi a, coneFiltrationLevel a) = a := by
  by_cases ha : a.val.maximum = k
  · simp only [coneFiltrationLevel, ite_eq_left ha, coneFromFiltration]
    apply Subtype.ext
    exact coneInsertTop_erase hi a ha
  · have hlt : a.val.maximum < k := lt_of_le_of_ne a.property ha
    simp only [coneFiltrationLevel, ite_eq_right ha, coneFromFiltration]
    apply Subtype.ext
    exact coneEraseTop_before hi a hlt

/-- The actual bottom and top reconstructions recover the complete preceding subset and its same interval coordinate. -/
theorem coneErase_fromFiltration {n : ℕ} {i k : Vertex.{u} n} (hi : i < k)
    (a : ConeBefore i k × Vertex.{u} 1) :
    (coneEraseTop hi (coneFromFiltration hi a), coneFiltrationLevel (coneFromFiltration hi a)) = a := by
  rcases a with ⟨a, ⟨t⟩⟩
  fin_cases t
  · apply Prod.ext
    · apply Subtype.ext
      exact coneEraseTop_before hi ⟨a.val, a.property.le⟩ a.property
    · simp [coneFiltrationLevel, coneFromFiltration, a.property.ne]
  · apply Prod.ext
    · simpa [coneFromFiltration] using coneEraseTop_insert hi a
    · simp [coneFiltrationLevel, coneFromFiltration, (coneInsertTop hi a).property]

/-- The actual cylinder-coordinate reconstruction preserves all original inclusions in both coordinates. -/
theorem coneFromFiltration_mono {n : ℕ} {i k : Vertex.{u} n} (hi : i < k) :
    Monotone (coneFromFiltration hi) := by
  rintro ⟨a, ⟨s⟩⟩ ⟨b, ⟨t⟩⟩ ⟨hab, hst⟩
  fin_cases s <;> fin_cases t
  · exact hab
  · exact Finset.Subset.trans hab (Finset.subset_insert _ _)
  · have h : ¬ (ULift.up (1 : Fin 2) : Vertex.{u} 1) ≤ ULift.up 0 := by decide
    exact False.elim (h hst)
  · exact coneInsertTop_mono hi hab

/-- The bounded original subset is the genuine two-layer cylinder on its preceding stage, with the complete
  native order in both directions. -/
def coneFiltrationOrderIso {n : ℕ} {i k : Vertex.{u} n} (hi : i < k) :
    ConeAtMost i k ≃o ConeBefore i k × Vertex.{u} 1 :=
  Equiv.toOrderIso
    { toFun a := (coneEraseTop hi a, coneFiltrationLevel a)
      invFun := coneFromFiltration hi
      left_inv := coneFromFiltration_erase hi
      right_inv := coneErase_fromFiltration hi }
    (fun _ _ h => ⟨coneEraseTop_mono hi h, coneFiltrationLevel_mono h⟩)
    (coneFromFiltration_mono hi)

end SSet.Marked.CoherentWeight
