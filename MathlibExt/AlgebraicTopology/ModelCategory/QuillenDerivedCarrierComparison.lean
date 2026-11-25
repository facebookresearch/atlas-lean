/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedEquivalence
public import MathlibExt.CategoryTheory.Localization.OriginalEquivalence

/-!
# Original carrier localization and its canonical derived comparison

Both strict localization lifts use the given carrier equivalence and the weak
classes of the two actual models. Their unit and counit are the lifts of its
original maps. The canonical derived comparison isomorphisms intertwine those
same units and counits on the entire localized categories.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u₁ u₂ v₁ v₂

open CategoryTheory MorphismProperty

namespace HomotopicalAlgebra.QuillenCarrierLocalization

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]

local notation "WC" => weakEquivalences C
local notation "WD" => weakEquivalences D

/-- The original forward carrier map followed by the actual target localization. -/
theorem forwardInverts (e : C ≌ D)
    (hL : WC ≤ (WD).inverseImage e.functor) :
    (WC).IsInvertedBy (e.functor ⋙ (WD).Q) :=
  fun _ _ f hf => Localization.inverts (WD).Q WD (e.functor.map f) (hL f hf)

/-- The original inverse carrier map followed by the actual source localization. -/
theorem inverseInverts (e : C ≌ D)
    (hR : WD ≤ (WC).inverseImage e.inverse) :
    (WD).IsInvertedBy (e.inverse ⋙ (WC).Q) :=
  fun _ _ f hf => Localization.inverts (WC).Q WC (e.inverse.map f) (hR f hf)

/-- The strict localization lift of the entire given forward carrier functor. -/
abbrev forward (e : C ≌ D) (hL : WC ≤ (WD).inverseImage e.functor) :
    (WC).Localization ⥤ (WD).Localization :=
  Localization.originalForward e WC WD (forwardInverts e hL)

/-- The strict localization lift of the entire original inverse carrier functor. -/
abbrev inverse (e : C ≌ D) (hR : WD ≤ (WC).inverseImage e.inverse) :
    (WD).Localization ⥤ (WC).Localization :=
  Localization.originalInverse e WC WD (inverseInverts e hR)

theorem forwardProjection (e : C ≌ D)
    (hL : WC ≤ (WD).inverseImage e.functor) :
    (WC).Q ⋙ forward e hL = e.functor ⋙ (WD).Q :=
  Localization.originalForward_projection e WC WD (forwardInverts e hL)

theorem inverseProjection (e : C ≌ D)
    (hR : WD ≤ (WC).inverseImage e.inverse) :
    (WD).Q ⋙ inverse e hR = e.inverse ⋙ (WC).Q :=
  Localization.originalInverse_projection e WC WD (inverseInverts e hR)

theorem forwardMapProjected (e : C ≌ D)
    (hL : WC ≤ (WD).inverseImage e.functor)
    {X Y : C} (f : X ⟶ Y) :
    (forward e hL).map ((WC).Q.map f) = (WD).Q.map (e.functor.map f) :=
  Localization.originalForward_map_projected e WC WD (forwardInverts e hL) f

theorem inverseMapProjected (e : C ≌ D)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    {X Y : D} (f : X ⟶ Y) :
    (inverse e hR).map ((WD).Q.map f) = (WC).Q.map (e.inverse.map f) :=
  Localization.originalInverse_map_projected e WC WD (inverseInverts e hR) f

theorem forwardInverseProjection (e : C ≌ D) (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse) :
    (WC).Q ⋙ (forward e hL ⋙ inverse e hR) = (e.functor ⋙ e.inverse) ⋙ (WC).Q :=
  Localization.originalForwardInverse_projection e WC WD
    (forwardInverts e hL) (inverseInverts e hR)

theorem inverseForwardProjection (e : C ≌ D) (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse) :
    (WD).Q ⋙ (inverse e hR ⋙ forward e hL) = (e.inverse ⋙ e.functor) ⋙ (WD).Q :=
  Localization.originalInverseForward_projection e WC WD
    (forwardInverts e hL) (inverseInverts e hR)

/-- The composite lift before applying the whole original carrier unit. -/
@[instance_reducible]
def forwardInverseLifting (e : C ≌ D) (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse) : Localization.Lifting (WC).Q WC
    ((e.functor ⋙ e.inverse) ⋙ (WC).Q) (forward e hL ⋙ inverse e hR) :=
  ⟨eqToIso (forwardInverseProjection e hL hR)⟩

/-- The composite lift before applying the whole original carrier counit. -/
@[instance_reducible]
def inverseForwardLifting (e : C ≌ D) (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse) : Localization.Lifting (WD).Q WD
    ((e.inverse ⋙ e.functor) ⋙ (WD).Q) (inverse e hR ⋙ forward e hL) :=
  ⟨eqToIso (inverseForwardProjection e hL hR)⟩

/-- The literal original carrier unit lifted through the chosen source localization. -/
abbrev unitIso (e : C ≌ D) (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse) :
    𝟭 (WC).Localization ≅ forward e hL ⋙ inverse e hR :=
  Localization.originalUnitIso e WC WD (forwardInverts e hL) (inverseInverts e hR)

/-- The literal original carrier counit lifted through the chosen target localization. -/
abbrev counitIso (e : C ≌ D) (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse) :
    inverse e hR ⋙ forward e hL ≅ 𝟭 (WD).Localization :=
  Localization.originalCounitIso e WC WD (forwardInverts e hL) (inverseInverts e hR)

theorem unitIsoHomProjected (e : C ≌ D)
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    (X : C) :
    (unitIso e hL hR).hom.app ((WC).Q.obj X) = (WC).Q.map (e.unitIso.hom.app X) :=
  Localization.originalUnitIso_hom_projected e WC WD (forwardInverts e hL) (inverseInverts e hR) X

theorem unitIsoInvProjected (e : C ≌ D)
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    (X : C) :
    (unitIso e hL hR).inv.app ((WC).Q.obj X) = (WC).Q.map (e.unitIso.inv.app X) :=
  Localization.originalUnitIso_inv_projected e WC WD (forwardInverts e hL) (inverseInverts e hR) X

theorem counitIsoHomProjected (e : C ≌ D)
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    (Y : D) :
    (counitIso e hL hR).hom.app ((WD).Q.obj Y) = (WD).Q.map (e.counitIso.hom.app Y) :=
  Localization.originalCounitIso_hom_projected e WC WD (forwardInverts e hL) (inverseInverts e hR) Y

theorem counitIsoInvProjected (e : C ≌ D)
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    (Y : D) :
    (counitIso e hL hR).inv.app ((WD).Q.obj Y) = (WD).Q.map (e.counitIso.inv.app Y) :=
  Localization.originalCounitIso_inv_projected e WC WD (forwardInverts e hL) (inverseInverts e hR) Y

theorem forwardUnitCounit (e : C ≌ D)
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    :
    Functor.whiskerRight (unitIso e hL hR).hom (forward e hL) ≫
      Functor.whiskerLeft (forward e hL) (counitIso e hL hR).hom = 𝟙 (forward e hL) :=
  Localization.originalForward_triangle e WC WD (forwardInverts e hL) (inverseInverts e hR)

/-- The actual carrier equivalence lifted with both original maps and the proved triangle. -/
abbrev equivalence (e : C ≌ D) (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse) : (WC).Localization ≌ (WD).Localization :=
  Localization.originalEquivalence e WC WD (forwardInverts e hL) (inverseInverts e hR)

theorem equivalenceFunctor (e : C ≌ D)
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse) :
    (equivalence e hL hR).functor = forward e hL := rfl

theorem equivalenceInverse (e : C ≌ D)
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse) :
    (equivalence e hL hR).inverse = inverse e hR := rfl

theorem equivalenceUnitIso (e : C ≌ D)
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse) :
    (equivalence e hL hR).unitIso = unitIso e hL hR := rfl

theorem equivalenceCounitIso (e : C ≌ D)
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse) :
    (equivalence e hL hR).counitIso = counitIso e hL hR := rfl

/-- The inverse carrier localization keeps the entire original forward counit inverse. -/
theorem inverseEquivalenceUnitIso (e : C ≌ D)
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    :
    (equivalence e.symm hR hL).unitIso = (equivalence e hL hR).counitIso.symm :=
  Localization.originalEquivalence_unitIso_symm e WC WD (forwardInverts e hL) (inverseInverts e hR)

/-- The inverse carrier localization keeps the entire original forward unit inverse. -/
theorem inverseEquivalenceCounitIso (e : C ≌ D)
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    :
    (equivalence e.symm hR hL).counitIso = (equivalence e hL hR).unitIso.symm :=
  Localization.originalEquivalence_counitIso_symm e WC WD
    (forwardInverts e hL) (inverseInverts e hR)

/-- The canonical left derived comparison extended to the entire original strict carrier lift. -/
def leftDerivedComparison (e : C ≌ D)
    [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor) :
    (quillenDerivedAdjunctionData e.toAdjunction).leftDerived ≅ forward e hL :=
  letI : IsIso (quillenDerivedAdjunctionData e.toAdjunction).leftComparison :=
      quillenDerived_leftComparison_isIso e.toAdjunction hL
  letI : Localization.Lifting (WC).Q WC (e.functor ⋙ (WD).Q) (quillenDerivedAdjunctionData
      e.toAdjunction).leftDerived :=
    ⟨asIso (quillenDerivedAdjunctionData e.toAdjunction).leftComparison⟩
  letI : Localization.Lifting (WC).Q WC (e.functor ⋙ (WD).Q) (forward e hL) :=
    ⟨eqToIso (forwardProjection e hL)⟩
  Localization.liftNatIso (WC).Q WC (e.functor ⋙ (WD).Q) (e.functor ⋙ (WD).Q)
    (quillenDerivedAdjunctionData e.toAdjunction).leftDerived (forward e hL) (Iso.refl _)

/-- The canonical right derived comparison extended from the entire original inverse lift. -/
def rightDerivedComparison (e : C ≌ D)
    [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hR : WD ≤ (WC).inverseImage e.inverse) :
    inverse e hR ≅ (quillenDerivedAdjunctionData e.toAdjunction).rightDerived :=
  letI : IsIso (quillenDerivedAdjunctionData e.toAdjunction).rightComparison :=
      quillenDerived_rightComparison_isIso e.toAdjunction hR
  letI : Localization.Lifting (WD).Q WD (e.inverse ⋙ (WC).Q) (quillenDerivedAdjunctionData
      e.toAdjunction).rightDerived :=
    ⟨(asIso (quillenDerivedAdjunctionData e.toAdjunction).rightComparison).symm⟩
  letI : Localization.Lifting (WD).Q WD (e.inverse ⋙ (WC).Q) (inverse e hR) :=
    ⟨eqToIso (inverseProjection e hR)⟩
  Localization.liftNatIso (WD).Q WD (e.inverse ⋙ (WC).Q) (e.inverse ⋙ (WC).Q)
    (inverse e hR) (quillenDerivedAdjunctionData e.toAdjunction).rightDerived (Iso.refl _)

theorem leftDerivedComparisonHomProjected (e : C ≌ D)
    [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (X : C) :
    (leftDerivedComparison e hL).hom.app ((WC).Q.obj X) = (quillenDerivedAdjunctionData
        e.toAdjunction).leftComparison.app X := by
  rw [leftDerivedComparison]
  simp only [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change (quillenDerivedAdjunctionData e.toAdjunction).leftComparison.app X ≫ 𝟙 _ ≫
    (eqToHom (forwardProjection e hL).symm).app X = _
  simp only [eqToHom_app]
  change (quillenDerivedAdjunctionData e.toAdjunction).leftComparison.app X ≫ 𝟙 _ ≫
    eqToHom rfl = _
  simp only [eqToHom_refl, Category.comp_id]

theorem rightDerivedComparisonHomProjected (e : C ≌ D)
    [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hR : WD ≤ (WC).inverseImage e.inverse)
    (Y : D) :
    (rightDerivedComparison e hR).hom.app ((WD).Q.obj Y) = (quillenDerivedAdjunctionData
        e.toAdjunction).rightComparison.app Y := by
  rw [rightDerivedComparison]
  simp only [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  change (eqToHom (inverseProjection e hR)).app Y ≫ 𝟙 _ ≫
    (quillenDerivedAdjunctionData e.toAdjunction).rightComparison.app Y = _
  simp only [eqToHom_app]
  change eqToHom rfl ≫ 𝟙 _ ≫
    (quillenDerivedAdjunctionData e.toAdjunction).rightComparison.app Y = _
  simp only [eqToHom_refl, Category.id_comp]

/-- The entire canonical derived unit and the original carrier unit have the same square. -/
theorem unitComparison (e : C ≌ D)
    [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    :
    (quillenDerivedAdjunctionData e.toAdjunction).adjunction.unit ≫
        Functor.whiskerRight (leftDerivedComparison e hL).hom (quillenDerivedAdjunctionData
            e.toAdjunction).rightDerived =
      (unitIso e hL hR).hom ≫
        Functor.whiskerLeft (forward e hL) (rightDerivedComparison e hR).hom := by
  apply Localization.natTrans_ext (WC).Q WC
  intro X
  change (quillenDerivedAdjunctionData e.toAdjunction).adjunction.unit.app ((WC).Q.obj X) ≫
      (quillenDerivedAdjunctionData e.toAdjunction).rightDerived.map ((leftDerivedComparison
          e hL).hom.app ((WC).Q.obj X)) =
    (unitIso e hL hR).hom.app ((WC).Q.obj X) ≫
      (rightDerivedComparison e hR).hom.app ((WD).Q.obj (e.functor.obj X))
  rw [leftDerivedComparisonHomProjected, unitIsoHomProjected,
    rightDerivedComparisonHomProjected]
  exact quillenDerived_unit_fac e.toAdjunction X

/-- The complete canonical derived counit agrees with the original carrier counit square. -/
theorem counitComparison (e : C ≌ D)
    [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    :
    Functor.whiskerRight (rightDerivedComparison e hR).hom (quillenDerivedAdjunctionData
        e.toAdjunction).leftDerived ≫
        (quillenDerivedAdjunctionData e.toAdjunction).adjunction.counit =
      Functor.whiskerLeft (inverse e hR) (leftDerivedComparison e hL).hom ≫
        (counitIso e hL hR).hom := by
  apply Localization.natTrans_ext (WD).Q WD
  intro Y
  change (quillenDerivedAdjunctionData e.toAdjunction).leftDerived.map
      ((rightDerivedComparison e hR).hom.app ((WD).Q.obj Y)) ≫
      (quillenDerivedAdjunctionData e.toAdjunction).adjunction.counit.app ((WD).Q.obj Y) =
    (leftDerivedComparison e hL).hom.app ((WC).Q.obj (e.inverse.obj Y)) ≫
      (counitIso e hL hR).hom.app ((WD).Q.obj Y)
  rw [rightDerivedComparisonHomProjected, leftDerivedComparisonHomProjected,
    counitIsoHomProjected]
  exact quillenDerived_counit_fac e.toAdjunction Y

end HomotopicalAlgebra.QuillenCarrierLocalization
