/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalMappingComposition

/-!
# Original fixed-edge triangle spaces and full relative coherence
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.FixedEdgeTriangle

open SegalHomotopy

variable (W : SimplicialSpace.{u}) (hW : segalSpaces W)
  (x y : (W.diagram _⦋0⦌) _⦋0⦌) (a : (mappingFibre W x y) _⦋0⦌)

/-- Insert the fixed original edge as the second edge of a y,x,y triangle. -/
def leftPair : mappingFibre W y x ⟶ mappingFibre W y x ⨯ mappingFibre W x y :=
  prod.lift (𝟙 _) (mappingFibre.snd W y x ≫ SSet.yonedaEquiv.symm a)

/-- Insert that same edge first, in the x,y,x triangle. -/
def rightPair : mappingFibre W y x ⟶ mappingFibre W x y ⨯ mappingFibre W y x :=
  prod.lift (mappingFibre.snd W y x ≫ SSet.yonedaEquiv.symm a) (𝟙 _)

/-- The original chosen pullback fixing the last edge of the y,x,y triangle. -/
abbrev leftTriangle : SSet.{u} := pullback (triangleComparison W y x y) (leftPair W x y a)

/-- The original chosen pullback fixing the first edge of the x,y,x triangle. -/
abbrev rightTriangle : SSet.{u} := pullback (triangleComparison W x y x) (rightPair W x y a)

/-- Retain the whole original left triangle projection. -/
def leftTriangleProjection : leftTriangle W x y a ⟶ triangleSpace W y x y :=
  pullback.fst _ _

/-- Retain the whole original right triangle projection. -/
def rightTriangleProjection : rightTriangle W x y a ⟶ triangleSpace W x y x :=
  pullback.fst _ _

/-- The left pullback's original varying-edge projection. -/
def leftProjection : leftTriangle W x y a ⟶ mappingFibre W y x := pullback.snd _ _

/-- The right pullback's original varying-edge projection. -/
def rightProjection : rightTriangle W x y a ⟶ mappingFibre W y x := pullback.snd _ _

/-- Both actual product projections of the left pair. -/
theorem leftPairLaws :
    leftPair W x y a ≫ prod.fst = 𝟙 _ ∧
    leftPair W x y a ≫ prod.snd = mappingFibre.snd W y x ≫ SSet.yonedaEquiv.symm a :=
  ⟨prod.lift_fst _ _, prod.lift_snd _ _⟩

/-- Both actual product projections of the right pair. -/
theorem rightPairLaws :
    rightPair W x y a ≫ prod.fst = mappingFibre.snd W y x ≫ SSet.yonedaEquiv.symm a ∧
    rightPair W x y a ≫ prod.snd = 𝟙 _ :=
  ⟨prod.lift_fst _ _, prod.lift_snd _ _⟩

/-- The constructed left pullback, its whole square and both original faces. -/
theorem leftGeometry :
    IsPullback (leftTriangleProjection W x y a) (leftProjection W x y a)
      (triangleComparison W y x y) (leftPair W x y a) ∧
    leftTriangleProjection W x y a ≫ triangleComparison W y x y =
      leftProjection W x y a ≫ leftPair W x y a ∧
    leftTriangleProjection W x y a ≫ triangleProjection W y x y ≫ W.diagram.δ (2 : Fin 3) =
      leftProjection W x y a ≫ mappingFibre.fst W y x ∧
    leftTriangleProjection W x y a ≫ triangleProjection W y x y ≫ W.diagram.δ (0 : Fin 3) =
      leftProjection W x y a ≫ mappingFibre.snd W y x ≫ SSet.yonedaEquiv.symm a ≫
        mappingFibre.fst W x y := by
  have hc : leftTriangleProjection W x y a ≫ triangleComparison W y x y =
      leftProjection W x y a ≫ leftPair W x y a := pullback.condition
  refine ⟨IsPullback.of_hasPullback _ _, hc, ?_, ?_⟩
  · rw [triangleProjection_first, ← Category.assoc, hc, Category.assoc,
      ← Category.assoc (leftPair W x y a), (leftPairLaws W x y a).1, Category.id_comp]
  · rw [triangleProjection_last, ← Category.assoc, hc, Category.assoc,
      ← Category.assoc (leftPair W x y a), (leftPairLaws W x y a).2, Category.assoc]

/-- The constructed right pullback keeps the other original fixed-face order. -/
theorem rightGeometry :
    IsPullback (rightTriangleProjection W x y a) (rightProjection W x y a)
      (triangleComparison W x y x) (rightPair W x y a) ∧
    rightTriangleProjection W x y a ≫ triangleComparison W x y x =
      rightProjection W x y a ≫ rightPair W x y a ∧
    rightTriangleProjection W x y a ≫ triangleProjection W x y x ≫ W.diagram.δ (2 : Fin 3) =
      rightProjection W x y a ≫ mappingFibre.snd W y x ≫ SSet.yonedaEquiv.symm a ≫
        mappingFibre.fst W x y ∧
    rightTriangleProjection W x y a ≫ triangleProjection W x y x ≫ W.diagram.δ (0 : Fin 3) =
      rightProjection W x y a ≫ mappingFibre.fst W y x := by
  have hc : rightTriangleProjection W x y a ≫ triangleComparison W x y x =
      rightProjection W x y a ≫ rightPair W x y a := pullback.condition
  refine ⟨IsPullback.of_hasPullback _ _, hc, ?_, ?_⟩
  · rw [triangleProjection_first, ← Category.assoc, hc, Category.assoc,
      ← Category.assoc (rightPair W x y a), (rightPairLaws W x y a).1, Category.assoc]
  · rw [triangleProjection_last, ← Category.assoc, hc, Category.assoc,
      ← Category.assoc (rightPair W x y a), (rightPairLaws W x y a).2, Category.id_comp]

include hW in
/-- Actual Segalness makes the original left projection a scalar trivial fibration. -/
theorem leftProjection_trivialFibration : trivialFibrations SSet.{u} (leftProjection W x y a) :=
  (trivialFibrations SSet.{u}).of_isPullback (leftGeometry W x y a).1
    (triangleComparison_trivialFibration W hW y x y)

include hW in
/-- The same base-change argument applies to the original right projection. -/
theorem rightProjection_trivialFibration : trivialFibrations SSet.{u} (rightProjection W x y a) :=
  (trivialFibrations SSet.{u}).of_isPullback (rightGeometry W x y a).1
    (triangleComparison_trivialFibration W hW x y x)

/-- Pull back the SAME accepted composition section on the left. -/
def leftSection : mappingFibre W y x ⟶ leftTriangle W x y a :=
  pullback.lift (leftPair W x y a ≫ mappingCompositionSection W hW y x y) (𝟙 _)
    (by rw [Category.assoc, mappingCompositionSection_comparison, Category.comp_id,
        Category.id_comp])

/-- Pull back the SAME accepted composition section on the right. -/
def rightSection : mappingFibre W y x ⟶ rightTriangle W x y a :=
  pullback.lift (rightPair W x y a ≫ mappingCompositionSection W hW x y x) (𝟙 _)
    (by rw [Category.assoc, mappingCompositionSection_comparison, Category.comp_id,
        Category.id_comp])

/-- Both strict section projections and the original left middle-face operator. -/
theorem leftSectionLaws :
    leftSection W hW x y a ≫ leftProjection W x y a = 𝟙 _ ∧
    leftSection W hW x y a ≫ leftTriangleProjection W x y a =
      leftPair W x y a ≫ mappingCompositionSection W hW y x y ∧
    leftSection W hW x y a ≫ leftTriangleProjection W x y a ≫ triangleMiddle W y x y =
      mappingPostcomposition W hW y x y a := by
  refine ⟨pullback.lift_snd _ _ _, pullback.lift_fst _ _ _, ?_⟩
  have hs : leftSection W hW x y a ≫ leftTriangleProjection W x y a =
      leftPair W x y a ≫ mappingCompositionSection W hW y x y := pullback.lift_fst _ _ _
  rw [← Category.assoc, hs, Category.assoc]
  rfl

/-- Both strict section projections and the original right middle-face operator. -/
theorem rightSectionLaws :
    rightSection W hW x y a ≫ rightProjection W x y a = 𝟙 _ ∧
    rightSection W hW x y a ≫ rightTriangleProjection W x y a =
      rightPair W x y a ≫ mappingCompositionSection W hW x y x ∧
    rightSection W hW x y a ≫ rightTriangleProjection W x y a ≫ triangleMiddle W x y x =
      mappingPrecomposition W hW x y x a := by
  refine ⟨pullback.lift_snd _ _ _, pullback.lift_fst _ _ _, ?_⟩
  have hs : rightSection W hW x y a ≫ rightTriangleProjection W x y a =
      rightPair W x y a ≫ mappingCompositionSection W hW x y x := pullback.lift_fst _ _ _
  rw [← Category.assoc, hs, Category.assoc]
  rfl

section ParameterLift
variable {T : SSet.{u}}

/-- Lift every original moving base cylinder and both prescribed left endpoints. -/
def leftLiftHomotopy (c : T ⊗ (Δ[1] : SSet.{u}) ⟶ mappingFibre W y x)
    (u₀ u₁ : T ⟶ leftTriangle W x y a)
    (h₀ : u₀ ≫ leftProjection W x y a = SSet.ι₀ ≫ c)
    (h₁ : u₁ ≫ leftProjection W x y a = SSet.ι₁ ≫ c) :
    {H : T ⊗ (Δ[1] : SSet.{u}) ⟶ leftTriangle W x y a //
      SSet.ι₀ ≫ H = u₀ ∧ SSet.ι₁ ≫ H = u₁ ∧ H ≫ leftProjection W x y a = c} := by
  have h₀' : (u₀ ≫ leftTriangleProjection W x y a) ≫ triangleComparison W y x y =
      SSet.ι₀ ≫ (c ≫ leftPair W x y a) := by
    rw [Category.assoc, (leftGeometry W x y a).2.1, ← Category.assoc, h₀, Category.assoc]
  have h₁' : (u₁ ≫ leftTriangleProjection W x y a) ≫ triangleComparison W y x y =
      SSet.ι₁ ≫ (c ≫ leftPair W x y a) := by
    rw [Category.assoc, (leftGeometry W x y a).2.1, ← Category.assoc, h₁, Category.assoc]
  let H := mappingCompositionLiftHomotopy W hW y x y (c ≫ leftPair W x y a)
    (u₀ ≫ leftTriangleProjection W x y a) (u₁ ≫ leftTriangleProjection W x y a) h₀' h₁'
  refine ⟨pullback.lift H.val c H.property.2.2, ?_, ?_, pullback.lift_snd _ _ _⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact H.property.1
    · rw [Category.assoc, pullback.lift_snd]
      exact h₀.symm
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact H.property.2.1
    · rw [Category.assoc, pullback.lift_snd]
      exact h₁.symm

/-- The right lift also retains its whole moving base and both endpoints. -/
def rightLiftHomotopy (c : T ⊗ (Δ[1] : SSet.{u}) ⟶ mappingFibre W y x)
    (u₀ u₁ : T ⟶ rightTriangle W x y a)
    (h₀ : u₀ ≫ rightProjection W x y a = SSet.ι₀ ≫ c)
    (h₁ : u₁ ≫ rightProjection W x y a = SSet.ι₁ ≫ c) :
    {H : T ⊗ (Δ[1] : SSet.{u}) ⟶ rightTriangle W x y a //
      SSet.ι₀ ≫ H = u₀ ∧ SSet.ι₁ ≫ H = u₁ ∧ H ≫ rightProjection W x y a = c} := by
  have h₀' : (u₀ ≫ rightTriangleProjection W x y a) ≫ triangleComparison W x y x =
      SSet.ι₀ ≫ (c ≫ rightPair W x y a) := by
    rw [Category.assoc, (rightGeometry W x y a).2.1, ← Category.assoc, h₀, Category.assoc]
  have h₁' : (u₁ ≫ rightTriangleProjection W x y a) ≫ triangleComparison W x y x =
      SSet.ι₁ ≫ (c ≫ rightPair W x y a) := by
    rw [Category.assoc, (rightGeometry W x y a).2.1, ← Category.assoc, h₁, Category.assoc]
  let H := mappingCompositionLiftHomotopy W hW x y x (c ≫ rightPair W x y a)
    (u₀ ≫ rightTriangleProjection W x y a) (u₁ ≫ rightTriangleProjection W x y a) h₀' h₁'
  refine ⟨pullback.lift H.val c H.property.2.2, ?_, ?_, pullback.lift_snd _ _ _⟩
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact H.property.1
    · rw [Category.assoc, pullback.lift_snd]
      exact h₀.symm
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      exact H.property.2.1
    · rw [Category.assoc, pullback.lift_snd]
      exact h₁.symm

end ParameterLift

/-- An actual left cylinder contracts to the SAME section, relative to its original projection. -/
def leftRelativeContraction :
    {H : SSet.Homotopy (𝟙 (leftTriangle W x y a))
        (leftProjection W x y a ≫ leftSection W hW x y a) //
      H.h ≫ leftProjection W x y a =
        fst (leftTriangle W x y a) (Δ[1] : SSet.{u}) ≫ leftProjection W x y a} := by
  let H := leftLiftHomotopy W hW x y a
    (fst (leftTriangle W x y a) (Δ[1] : SSet.{u}) ≫ leftProjection W x y a)
    (𝟙 _) (leftProjection W x y a ≫ leftSection W hW x y a)
    (by simp only [Category.id_comp, SSet.ι₀_fst_assoc])
    (by simp only [Category.assoc, (leftSectionLaws W hW x y a).1,
      Category.comp_id, SSet.ι₁_fst_assoc])
  exact ⟨{ h := H.val
           h₀ := H.property.1
           h₁ := H.property.2.1
           rel := by ext n ⟨⟨v, hv⟩, t⟩ <;> cases hv }, H.property.2.2⟩

/-- The analogous right cylinder fixes the parameter through fst, not the interval through snd. -/
def rightRelativeContraction :
    {H : SSet.Homotopy (𝟙 (rightTriangle W x y a))
        (rightProjection W x y a ≫ rightSection W hW x y a) //
      H.h ≫ rightProjection W x y a =
        fst (rightTriangle W x y a) (Δ[1] : SSet.{u}) ≫ rightProjection W x y a} := by
  let H := rightLiftHomotopy W hW x y a
    (fst (rightTriangle W x y a) (Δ[1] : SSet.{u}) ≫ rightProjection W x y a)
    (𝟙 _) (rightProjection W x y a ≫ rightSection W hW x y a)
    (by simp only [Category.id_comp, SSet.ι₀_fst_assoc])
    (by simp only [Category.assoc, (rightSectionLaws W hW x y a).1,
      Category.comp_id, SSet.ι₁_fst_assoc])
  exact ⟨{ h := H.val
           h₀ := H.property.1
           h₁ := H.property.2.1
           rel := by ext n ⟨⟨v, hv⟩, t⟩ <;> cases hv }, H.property.2.2⟩

end SimplicialSpace.FixedEdgeTriangle
