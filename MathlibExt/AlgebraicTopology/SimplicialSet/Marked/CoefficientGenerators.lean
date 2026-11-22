/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoefficientModel
import MathlibExt.CategoryTheory.MorphismProperty.AdjointFamily

/-!
# The exact genuine coefficient generator families

Both families are the actual inverse images of the proved point-slice
mono and full weak-mono families. Their genuine source-smallness and
full right-class equalities come from those original families and the
canonical point equivalence. The marked carrier, whole maps and value
universe are unchanged; no generator or model outcome is an input.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped Simplicial

namespace SSet.Marked

attribute [local instance] coefficientMarkedModelCategory

/-- Actual coefficient generating monos retain every original point-slice generator under the canonical inverse. -/
def coefficientGeneratingMonos : MorphismProperty Marked.{u} :=
  (overCells monoCell.{u} (max (Δ[0] : SSet.{u}))).strictMap coefficientPointEquivalence.inverse

/-- The full proved original coefficient weak-mono family is transported by the same genuine inverse functor. -/
def coefficientGeneratingWeakMonos : MorphismProperty Marked.{u} :=
  (cartesianMarkedWeakCells (Δ[0] : SSet.{u})).strictMap coefficientPointEquivalence.inverse

/-- Genuine original source eligibility proves coefficient-mono family smallness at the original universe. -/
theorem coefficientGeneratingMonos_isSmall : coefficientGeneratingMonos.{u}.IsSmall.{u} := by
  let _ : (overCells monoCell.{u} (max (Δ[0] : SSet.{u}))).HasSmallObjectArgument.{u} :=
    fixedBaseMonoCells_hasSmallObjectArgument _
  obtain ⟨κ, hκ, hb, hI⟩ := (inferInstance :
    (overCells monoCell.{u} (max (Δ[0] : SSet.{u}))).HasSmallObjectArgument.{u}).exists_cardinal
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hb
  exact IsSmall.strictMap hI.isSmall coefficientPointEquivalence.inverse

/-- The genuinely produced full weak-mono family is small in the unchanged coefficient universe. -/
theorem coefficientGeneratingWeakMonos_isSmall : coefficientGeneratingWeakMonos.{u}.IsSmall.{u} := by
  let _ : (cartesianMarkedWeakCells (Δ[0] : SSet.{u})).HasSmallObjectArgument.{u} :=
    cartesianMarkedWeakCells_hasSmallObjectArgument _
  obtain ⟨κ, hκ, hb, hJ⟩ := (inferInstance :
    (cartesianMarkedWeakCells (Δ[0] : SSet.{u})).HasSmallObjectArgument.{u}).exists_cardinal
  let _ : Fact κ.IsRegular := hκ
  let _ : OrderBot κ.ord.ToType := hb
  exact IsSmall.strictMap hJ.isSmall coefficientPointEquivalence.inverse

/-- The exact coefficient mono-family right class is the full original marked trivial-fibration class. -/
theorem coefficientGeneratingMonos_rlp : coefficientGeneratingMonos.{u}.rlp = trivialFibrations Marked.{u} := by
  let _ := markedCofibrationStructure (max (Δ[0] : SSet.{u}))
  let _ := cartesianMarkedFibrationStructure (Δ[0] : SSet.{u})
  let _ := cartesianMarkedWeakStructure (Δ[0] : SSet.{u})
  let _ := cartesianMarkedModelCategory (Δ[0] : SSet.{u})
  have hi : (overCells monoCell.{u} (max (Δ[0] : SSet.{u}))).rlp =
      trivialFibrations (Over (max (Δ[0] : SSet.{u}))) :=
    (fixedBaseMonoCells_rlp_eq _).trans (cofibrations_rlp _)
  unfold coefficientGeneratingMonos
  rw [strictMap_rlp_eq_inverseImage_rlp _ coefficientPointEquivalence.inverse
    coefficientPointEquivalence.functor coefficientPointEquivalence.symm.toAdjunction, hi]
  rfl

/-- The exact full coefficient weak-mono-family right class is the original marked fibration class. -/
theorem coefficientGeneratingWeakMonos_rlp : coefficientGeneratingWeakMonos.{u}.rlp = fibrations Marked.{u} := by
  let _ := markedCofibrationStructure (max (Δ[0] : SSet.{u}))
  let _ := cartesianMarkedFibrationStructure (Δ[0] : SSet.{u})
  let _ := cartesianMarkedWeakStructure (Δ[0] : SSet.{u})
  let _ := cartesianMarkedModelCategory (Δ[0] : SSet.{u})
  unfold coefficientGeneratingWeakMonos
  rw [strictMap_rlp_eq_inverseImage_rlp _ coefficientPointEquivalence.inverse
    coefficientPointEquivalence.functor coefficientPointEquivalence.symm.toAdjunction,
      cartesianMarkedWeakCells_right_eq]
  rfl

/-- The genuine original coefficient right classes satisfy the full marked weak-class intersection required
  by recognition. -/
theorem coefficientGenerating_right_intersection :
    coefficientGeneratingMonos.{u}.rlp =
      coefficientGeneratingWeakMonos.{u}.rlp ⊓ weakEquivalences Marked.{u} := by
  rw [coefficientGeneratingMonos_rlp, coefficientGeneratingWeakMonos_rlp]
  rfl

/-- Each actual full coefficient weak-mono generator is a genuine trivial cofibration for the same
  transported marked model. -/
theorem coefficientGeneratingWeakMonos_le_trivialCofibrations :
    coefficientGeneratingWeakMonos.{u} ≤ trivialCofibrations Marked.{u} := by
  rw [← fibrations_llp, ← coefficientGeneratingWeakMonos_rlp]
  exact coefficientGeneratingWeakMonos.le_llp_rlp

end SSet.Marked
