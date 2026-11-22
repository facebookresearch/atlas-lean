/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightMappingJoyalPointedHom
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFixedFrontReedyFactorization
import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyRepresentableTrivialFibration
import MathlibExt.AlgebraicTopology.ModelCategory.FibrantUnderObjects

/-!
# The actual pointed Reedy replacement mapping comparison

A quasicategory with its original two endpoint maps is fibrant in the
actual named Under Joyal model. Its opposite is cofibrant. The genuine
original relative matching trivial fibrations therefore give a Kan
trivial fibration of full original mapping spaces. The target is the
same original right-mapping space, through its literal pointed Hom iso.
-/

noncomputable section

universe u

open CategoryTheory Opposite Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

attribute [local instance] JoyalSSet.modelCategory

namespace CategoryTheory.CoherentRealization.OriginalRawRightMapping

open OriginalFixedFrontContraction

variable {K : SSet.{u}} (a b : (Δ[0] : SSet.{u}) ⟶ K)

/-- The original copied endpoint-fixed input is fibrant exactly when its full original carrier is a quasicategory. -/
theorem pointedInput_isFibrant_iff :
    IsFibrant (pointedCopyFunctor.obj (pointedInput a b)) ↔ SSet.Quasicategory K := by
  exact (isFibrant_under_iff _ _).trans (JoyalSSet.isFibrant_iff_quasicategory _)

/-- The opposite of the same endpoint-fixed quasicategory input is genuinely cofibrant in the original opposite
model. -/
theorem pointedInput_op_isCofibrant [SSet.Quasicategory K] :
    IsCofibrant (op (pointedCopyFunctor.obj (pointedInput a b))) := by
  let A : PointedJoyal.{u} := pointedCopyFunctor.obj (pointedInput a b)
  have hA : IsFibrant A := (pointedInput_isFibrant_iff a b).mpr inferInstance
  let _ : Fibration (terminal.from A) := hA
  exact (isCofibrant_iff_of_isInitial (terminal.from A).op
    (initialOpOfTerminal terminalIsTerminal)).mpr inferInstance

/-- The full original Reedy replacement Hom space, retaining the generated pointed objects and both endpoints. -/
def reedyHomSpace : SSet.{u} :=
  reedyReplacement.op ⋙ yoneda.obj (pointedCopyFunctor.obj (pointedInput a b))

/-- Restriction along the actual generated Reedy replacement map, with no replacement of its morphisms. -/
def reedyHomComparison : reedyHomSpace a b ⟶ pointedJoyalHomSpace a b :=
  (Functor.isoWhiskerLeft reversedFactorization.Z
    (CategoryTheory.Coyoneda.objOpOp (pointedCopyFunctor.obj (pointedInput a b)))).inv ≫
    Functor.whiskerRight reversedFactorization.p
      (coyoneda.obj (op (op (pointedCopyFunctor.obj (pointedInput a b))))) ≫
      (Functor.isoWhiskerLeft pointedJoyalDiagram.op
        (CategoryTheory.Coyoneda.objOpOp (pointedCopyFunctor.obj (pointedInput a b)))).hom

/-- Every complete original replacement Hom simplex restricts along the same generated pointed map. -/
theorem reedyHomComparison_app (n : ℕ)
    (g : reedyReplacement.obj ⦋n⦌ ⟶ pointedCopyFunctor.obj (pointedInput a b)) :
    (reedyHomComparison a b).app (op ⦋n⦌) g = reedyReplacementMap.app ⦋n⦌ ≫ g := by
  apply Under.UnderMorphism.ext
  rfl

/-- For the same actual quasicategory input, the full original replacement comparison is a Kan trivial fibration. -/
theorem reedyHomComparison_trivialFibration [SSet.Quasicategory K] :
    trivialFibrations SSet.{u} (reedyHomComparison a b) := by
  let _ : IsCofibrant (op (pointedCopyFunctor.obj (pointedInput a b))) :=
    pointedInput_op_isCofibrant a b
  have h := SimplicialObject.representable_reedy_trivialFibration
    (op (pointedCopyFunctor.obj (pointedInput a b))) reversedFactorization.p
    reversedFactorization_relativeMatching_trivial
  let e := Functor.isoWhiskerLeft reversedFactorization.Z
    (CategoryTheory.Coyoneda.objOpOp (pointedCopyFunctor.obj (pointedInput a b)))
  let d := Functor.isoWhiskerLeft pointedJoyalDiagram.op
    (CategoryTheory.Coyoneda.objOpOp (pointedCopyFunctor.obj (pointedInput a b)))
  change trivialFibrations SSet.{u} (e.inv ≫ _ ≫ d.hom)
  exact (trivialFibrations SSet.{u}).comp_mem _ _
    ((trivialFibrations SSet.{u}).of_isIso e.inv)
    ((trivialFibrations SSet.{u}).comp_mem _ _ h
      ((trivialFibrations SSet.{u}).of_isIso d.hom))

/-- The actual replacement maps to the same original right-mapping space by its full pointed Hom inverse. -/
def reedyRightMappingComparison : reedyHomSpace a b ⟶ SSet.mappingSpaceRight K a b :=
  reedyHomComparison a b ≫ (pointedJoyalHomSpaceIso a b).inv

end CategoryTheory.CoherentRealization.OriginalRawRightMapping
