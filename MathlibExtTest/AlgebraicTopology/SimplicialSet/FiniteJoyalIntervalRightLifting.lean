/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalRightLifting

/-!
# Public consumers of the finite-interval right-lifting criterion
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
  MonoidalCategory CartesianMonoidalCategory

universe u

namespace SSet.joyalInterval.RightLiftingTest

variable {A B X Y : SSet.{u}} (i : A ⟶ B) (p : X ⟶ Y) (ε : Fin 2)

/-- The criterion gives an actual raw inner-fibration instance over any base. -/
theorem isInnerFibration (hp : auxiliaryNaiveFibrations p) : InnerFibration p :=
  ((auxiliaryNaiveFibrations_iff p).mp hp).1

/-- Both endpoint boundary-RLP hypotheses assemble the auxiliary class,
without a quasicategory or model-category premise. -/
theorem of_endpoint_lifting (hp : InnerFibration p)
    (h : ∀ ε : Fin 2, modelCategoryQuillen.I.rlp (endpointFunctionMap p ε)) :
    auxiliaryNaiveFibrations p :=
  (auxiliaryNaiveFibrations_iff p).mpr ⟨hp, h⟩

/-- A fully prescribed square gives both original and transposed strict
diagonal equations. The transposed diagonal is the actual curry of the first. -/
theorem lift_with_transposed_equations [Mono i] (hp : auxiliaryNaiveFibrations p)
    (α : Arrow.mk (productPrecylinder.endpointCorner i ε) ⟶ Arrow.mk p) :
    let β := MonoidalClosed.internalHomAdjunction₂.arrowHomEquiv
      (endpointCornerPushoutObjObj i ε) (endpointFunctionPullbackObjObj p ε) α
    ∃ (l : joyalInterval ⊗ B ⟶ X) (m : B ⟶ (ihom joyalInterval).obj X),
      productPrecylinder.endpointCorner i ε ≫ l = α.left ∧ l ≫ p = α.right ∧
      i ≫ m = β.left ∧ m ≫ endpointFunctionMap p ε = β.right ∧
      m = MonoidalClosed.curry l := by
  dsimp only
  have hEP := ((auxiliaryNaiveFibrations_iff_monomorphisms p).mp hp).2 ε i
    (MorphismProperty.monomorphisms.infer_property i)
  have hLP := (endpointCorner_hasLiftingProperty_iff i p ε).mpr hEP
  obtain ⟨l⟩ := (Arrow.hasLiftingProperty_iff _ _).mp hLP α
  let m := MonoidalClosed.internalHomAdjunction₂.liftStructEquiv
    (endpointCornerPushoutObjObj i ε) (endpointFunctionPullbackObjObj p ε) α l
  exact ⟨l.l, m.l, l.fac_left, l.fac_right, m.fac_left, m.fac_right, rfl⟩

/-- The transposed pullback components retain the supplied base map and
the prescribed endpoint, including the native unit identification. -/
theorem transposed_components
    (α : Arrow.mk (productPrecylinder.endpointCorner i ε) ⟶ Arrow.mk p) :
    let β := MonoidalClosed.internalHomAdjunction₂.arrowHomEquiv
      (endpointCornerPushoutObjObj i ε) (endpointFunctionPullbackObjObj p ε) α
    β.right ≫ pullback.fst (endpointEvaluation Y ε) p = MonoidalClosed.curry α.right ∧
      β.right ≫ pullback.snd (endpointEvaluation Y ε) p =
        pushout.inl i ((productPrecylinder.app A).endpoint ε) ≫ α.left := by
  dsimp only
  constructor
  · exact MonoidalClosed.internalHomAdjunction₂.arrowHomEquiv_apply_right_snd
      (endpointCornerPushoutObjObj i ε) (endpointFunctionPullbackObjObj p ε) α
  · apply (cancel_mono ((MonoidalClosed.unitNatIso (C := SSet.{u})).hom.app X)).mp
    rw [Category.assoc]
    change (MonoidalClosed.internalHomAdjunction₂.arrowHomEquiv
      (endpointCornerPushoutObjObj i ε) (endpointFunctionPullbackObjObj p ε) α).right ≫
        (endpointFunctionPullbackObjObj p ε).fst = _
    rw [ParametrizedAdjunction.arrowHomEquiv_apply_right_fst]
    let t := pushout.inl i ((productPrecylinder.app A).endpoint ε) ≫ α.left
    change MonoidalClosed.curry ((λ_ B).hom ≫ t) =
      t ≫ (MonoidalClosed.unitNatIso (C := SSet.{u})).hom.app X
    have hunit : MonoidalClosed.curry (λ_ B).hom =
        (MonoidalClosed.unitNatIso (C := SSet.{u})).hom.app B := by
      simp [MonoidalClosed.unitNatIso, MonoidalClosed.curry_eq]
    rw [MonoidalClosed.curry_natural_right, hunit]
    exact ((MonoidalClosed.unitNatIso (C := SSet.{u})).hom.naturality t).symm

end SSet.joyalInterval.RightLiftingTest
