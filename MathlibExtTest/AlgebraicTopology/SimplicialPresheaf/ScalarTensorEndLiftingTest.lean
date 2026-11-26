/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialPresheaf.ScalarTensorEndLifting

/-! # Original scalar tensor/end corner and filler clients -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w

open CategoryTheory Opposite

namespace ScalarTensorEndLiftingTest

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {A B X Y : SimplicialPresheaf.{u} D} {K L : SSet.{u}}
  (i : A ⟶ B) (j : K ⟶ L) (p : X ⟶ Y)
  (pp : (SimplicialPresheaf.scalarTensor (D := D)).PushoutObjObj i j)
  (pb : (SimplicialPresheaf.innerHomFunctor (D := D)).PullbackObjObj i p)

/-- Every original square has all three actual transposed corner legs. -/
theorem arrowSquareLegs (α : Arrow.mk pp.ι ⟶ Arrow.mk p) :
    let β := (SimplicialPresheaf.scalarTensorHomAdjunction₂ (D := D)).arrowHomEquiv pp pb α
    β.left = SimplicialPresheaf.scalarTensorHomEquiv B K X (pp.inl ≫ α.left) ∧
      β.right ≫ pb.fst = SimplicialPresheaf.scalarTensorHomEquiv A L X (pp.inr ≫ α.left) ∧
      β.right ≫ pb.snd = SimplicialPresheaf.scalarTensorHomEquiv B L Y α.right := by
  dsimp only
  rw [← SimplicialPresheaf.scalarTensorHomAdjunction₂_homEquiv B K X,
    ← SimplicialPresheaf.scalarTensorHomAdjunction₂_homEquiv A L X,
    ← SimplicialPresheaf.scalarTensorHomAdjunction₂_homEquiv B L Y]
  exact ⟨rfl,
    (SimplicialPresheaf.scalarTensorHomAdjunction₂ (D := D)).arrowHomEquiv_apply_right_fst pp pb α,
    (SimplicialPresheaf.scalarTensorHomAdjunction₂ (D := D)).arrowHomEquiv_apply_right_snd pp pb α⟩

/-- Both original pushout injections retain the actual inverse transposition. -/
theorem inverseSquareLegs (β : Arrow.mk j ⟶ Arrow.mk pb.π) :
    let α := ((SimplicialPresheaf.scalarTensorHomAdjunction₂ (D := D)).arrowHomEquiv pp pb).symm β
    pp.inl ≫ α.left = (SimplicialPresheaf.scalarTensorHomEquiv B K X).symm β.left ∧
      pp.inr ≫ α.left = (SimplicialPresheaf.scalarTensorHomEquiv A L X).symm (β.right ≫ pb.fst) := by
  dsimp only
  rw [← SimplicialPresheaf.scalarTensorHomAdjunction₂_homEquiv B K X,
    ← SimplicialPresheaf.scalarTensorHomAdjunction₂_homEquiv A L X]
  exact ⟨(SimplicialPresheaf.scalarTensorHomAdjunction₂ (D := D)).inl_arrowHomEquiv_symm_apply_left pp pb β,
    (SimplicialPresheaf.scalarTensorHomAdjunction₂ (D := D)).inr_arrowHomEquiv_symm_apply_left pp pb β⟩

/-- Transposing and untransposing gives the same two original square maps. -/
theorem arrowSquareRoundTrip (α : Arrow.mk pp.ι ⟶ Arrow.mk p) :
    ((SimplicialPresheaf.scalarTensorHomAdjunction₂ (D := D)).arrowHomEquiv pp pb).symm
      ((SimplicialPresheaf.scalarTensorHomAdjunction₂ (D := D)).arrowHomEquiv pp pb α) = α :=
  Equiv.symm_apply_apply _ α

/-- Every original lift transposes with both original strict filler equations. -/
theorem transposedFillerLegs (α : Arrow.mk pp.ι ⟶ Arrow.mk p) (l : Arrow.LiftStruct α) :
    let β := (SimplicialPresheaf.scalarTensorHomAdjunction₂ (D := D)).arrowHomEquiv pp pb α
    let t := (SimplicialPresheaf.scalarTensorHomAdjunction₂ (D := D)).liftStructEquiv pp pb α l
    t.l = SimplicialPresheaf.scalarTensorHomEquiv B L X l.l ∧
      j ≫ t.l = β.left ∧ t.l ≫ pb.π = β.right := by
  dsimp only
  rw [← SimplicialPresheaf.scalarTensorHomAdjunction₂_homEquiv B L X]
  let t := (SimplicialPresheaf.scalarTensorHomAdjunction₂ (D := D)).liftStructEquiv pp pb α l
  exact ⟨rfl, t.fac_left, t.fac_right⟩

/-- The two original arrows have exactly equivalent lifting properties. -/
theorem liftingProperty_iff : HasLiftingProperty pp.ι p ↔ HasLiftingProperty j pb.π :=
  (SimplicialPresheaf.scalarTensorHomAdjunction₂ (D := D)).hasLiftingProperty_iff pp pb

end ScalarTensorEndLiftingTest
