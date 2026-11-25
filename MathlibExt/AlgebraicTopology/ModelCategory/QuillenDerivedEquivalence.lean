/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedAdjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived

/-!
# The given canonical derived adjunction of a homotopical adjoint equivalence

The original functors preserve weak equivalences on all objects. Their canonical total
derived comparison maps are therefore isomorphisms. The derived unit and counit retain
their original factorization equations and become isomorphisms on every localized object.
The resulting equivalence uses the same two canonical derived functors and adjunction.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u₁ u₂ v₁ v₂

open CategoryTheory MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [CategoryTheory.Adjunction.IsQuillenAdjunction adj]

local notation "WC" => weakEquivalences C
local notation "WD" => weakEquivalences D
local notation "data" => quillenDerivedAdjunctionData adj

/-- The actual canonical left comparison is invertible for the given homotopical functor. -/
theorem quillenDerived_leftComparison_isIso
    (hL : WC ≤ (WD).inverseImage L) : IsIso (data).leftComparison := by
  let _ : (data).leftDerived.IsLeftDerivedFunctor (data).leftComparison WC := (data).leftIsDerived
  apply Functor.isIso_of_isLeftDerivedFunctor_of_inverts (W := WC)
    (data).leftDerived (data).leftComparison
  intro X Y f hf
  exact Localization.inverts (WD).Q WD (L.map f) (hL f hf)

/-- The whole canonical right comparison is invertible for the original homotopical functor. -/
theorem quillenDerived_rightComparison_isIso
    (hR : WD ≤ (WC).inverseImage R) : IsIso (data).rightComparison := by
  let _ : (data).rightDerived.IsRightDerivedFunctor (data).rightComparison WD :=
    (data).rightIsDerived
  apply Functor.isIso_of_isRightDerivedFunctor_of_inverts (W := WD)
    (data).rightDerived (data).rightComparison
  intro X Y f hf
  exact Localization.inverts (WC).Q WC (R.map f) (hR f hf)

/-- The full actual canonical unit has the original derived-unit factorization equation. -/
theorem quillenDerived_unit_fac (X : C) :
    (data).adjunction.unit.app ((WC).Q.obj X) ≫
      (data).rightDerived.map ((data).leftComparison.app X) =
      (WC).Q.map (adj.unit.app X) ≫ (data).rightComparison.app (L.obj X) := by
  let _ : (data).leftDerived.IsLeftDerivedFunctor (data).leftComparison WC := (data).leftIsDerived
  let _ : (data).rightDerived.IsRightDerivedFunctor (data).rightComparison WD :=
    (data).rightIsDerived
  let _ : ((data).leftDerived ⋙ (data).rightDerived).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (data).leftComparison (data).rightDerived)
      WC := (data).leftCompositeIsDerived
  let _ : ((data).rightDerived ⋙ (data).leftDerived).IsRightDerivedFunctor
      (Functor.whiskerRight (data).rightComparison (data).leftDerived ≫
        (Functor.associator _ _ _).hom) WD := (data).rightCompositeIsDerived
  change (adj.derivedη WC (data).leftComparison (data).rightComparison).app ((WC).Q.obj X) ≫
      (data).rightDerived.map ((data).leftComparison.app X) = _
  exact adj.derivedη_fac_app WC (data).leftComparison (data).rightComparison X

/-- The original canonical counit retains its whole derived-counit factorization equation. -/
theorem quillenDerived_counit_fac (Y : D) :
    (data).leftDerived.map ((data).rightComparison.app Y) ≫
      (data).adjunction.counit.app ((WD).Q.obj Y) =
      (data).leftComparison.app (R.obj Y) ≫ (WD).Q.map (adj.counit.app Y) := by
  let _ : (data).leftDerived.IsLeftDerivedFunctor (data).leftComparison WC := (data).leftIsDerived
  let _ : (data).rightDerived.IsRightDerivedFunctor (data).rightComparison WD :=
    (data).rightIsDerived
  let _ : ((data).leftDerived ⋙ (data).rightDerived).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (data).leftComparison (data).rightDerived)
      WC := (data).leftCompositeIsDerived
  let _ : ((data).rightDerived ⋙ (data).leftDerived).IsRightDerivedFunctor
      (Functor.whiskerRight (data).rightComparison (data).leftDerived ≫
        (Functor.associator _ _ _).hom) WD := (data).rightCompositeIsDerived
  change (data).leftDerived.map ((data).rightComparison.app Y) ≫
      (adj.derivedε WD (data).leftComparison (data).rightComparison).app ((WD).Q.obj Y) = _
  exact adj.derivedε_fac_app WD (data).leftComparison (data).rightComparison Y

/-- The same given canonical unit is an isomorphism on every original localized object. -/
theorem quillenDerived_unit_isIso [IsIso adj.unit]
    (hL : WC ≤ (WD).inverseImage L) (hR : WD ≤ (WC).inverseImage R) :
    IsIso (data).adjunction.unit := by
  let _ : IsIso (data).leftComparison := quillenDerived_leftComparison_isIso adj hL
  let _ : IsIso (data).rightComparison := quillenDerived_rightComparison_isIso adj hR
  let _ : (WC).Q.EssSurj := Localization.essSurj (WC).Q WC
  let _ : ∀ Y, IsIso ((data).adjunction.unit.app Y) := fun Y => by
    rw [NatTrans.isIso_app_iff_of_iso _ ((WC).Q.objObjPreimageIso Y).symm]
    exact IsIso.of_isIso_fac_right (quillenDerived_unit_fac adj _)
  exact NatIso.isIso_of_isIso_app (data).adjunction.unit

/-- The actual canonical counit is invertible on the entire original target localization. -/
theorem quillenDerived_counit_isIso [IsIso adj.counit]
    (hL : WC ≤ (WD).inverseImage L) (hR : WD ≤ (WC).inverseImage R) :
    IsIso (data).adjunction.counit := by
  let _ : IsIso (data).leftComparison := quillenDerived_leftComparison_isIso adj hL
  let _ : IsIso (data).rightComparison := quillenDerived_rightComparison_isIso adj hR
  let _ : (WD).Q.EssSurj := Localization.essSurj (WD).Q WD
  let _ : ∀ Y, IsIso ((data).adjunction.counit.app Y) := fun Y => by
    rw [NatTrans.isIso_app_iff_of_iso _ ((WD).Q.objObjPreimageIso Y).symm]
    exact IsIso.of_isIso_fac_left (quillenDerived_counit_fac adj _)
  exact NatIso.isIso_of_isIso_app (data).adjunction.counit

/-- Upgrade the actual given derived adjunction, retaining both canonical derived functors. -/
def homotopicalQuillenDerivedEquivalence [IsIso adj.unit] [IsIso adj.counit]
    (hL : WC ≤ (WD).inverseImage L) (hR : WD ≤ (WC).inverseImage R) :
    (WC).Localization ≌ (WD).Localization := by
  let _ : IsIso (data).adjunction.unit := quillenDerived_unit_isIso adj hL hR
  let _ : IsIso (data).adjunction.counit := quillenDerived_counit_isIso adj hL hR
  exact (data).adjunction.toEquivalence

variable [IsIso adj.unit] [IsIso adj.counit]
  (hL : weakEquivalences C ≤ (weakEquivalences D).inverseImage L)
  (hR : weakEquivalences D ≤ (weakEquivalences C).inverseImage R)

/-- The entire forward functor is the original given canonical total left derived functor. -/
theorem homotopicalQuillenDerivedEquivalence_functor :
    (homotopicalQuillenDerivedEquivalence adj hL hR).functor = (data).leftDerived := rfl

/-- The entire inverse functor keeps the same original total right derived functor. -/
theorem homotopicalQuillenDerivedEquivalence_inverse :
    (homotopicalQuillenDerivedEquivalence adj hL hR).inverse = (data).rightDerived := rfl

/-- The complete unit isomorphism has the actual original derived-adjunction unit map. -/
theorem homotopicalQuillenDerivedEquivalence_unit_hom :
    (homotopicalQuillenDerivedEquivalence adj hL hR).unitIso.hom = (data).adjunction.unit := rfl

/-- The entire counit isomorphism keeps the original derived-adjunction counit map. -/
theorem homotopicalQuillenDerivedEquivalence_counit_hom :
    (homotopicalQuillenDerivedEquivalence adj hL hR).counitIso.hom =
      (data).adjunction.counit := rfl

/-- Every full original Hom map agrees with the actual canonical derived adjunction. -/
theorem homotopicalQuillenDerivedEquivalence_homEquiv (X : (WC).Localization)
    (Y : (WD).Localization) (f : (data).leftDerived.obj X ⟶ Y) :
    (homotopicalQuillenDerivedEquivalence adj hL hR).toAdjunction.homEquiv X Y f =
      (data).adjunction.homEquiv X Y f := rfl

end HomotopicalAlgebra
