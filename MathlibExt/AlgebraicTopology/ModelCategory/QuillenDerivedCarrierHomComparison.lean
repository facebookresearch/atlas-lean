/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedCarrierComparison

/-!
# Complete Hom transport for the original carrier and derived adjunctions

Use the actual canonical derived record and the two already proved carrier
comparison isomorphisms. Both complete Hom functions retain their original
adjunction choices; the unit comparison proves equality on every localized
arrow. No adjunction compatibility law is supplied as a premise.
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

/-- The entire carrier Hom equivalence transported by the two actual derived comparisons. -/
def transportedHomEquiv (e : C ≌ D) [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    (X : (WC).Localization) (Y : (WD).Localization) :
    ((quillenDerivedAdjunctionData e.toAdjunction).leftDerived.obj X ⟶ Y) ≃
      (X ⟶ (quillenDerivedAdjunctionData e.toAdjunction).rightDerived.obj Y) :=
  let α := leftDerivedComparison e hL
  let β := rightDerivedComparison e hR
  let carrier : Localization.originalForward e WC WD (forwardInverts e hL) ⊣
    Localization.originalInverse e WC WD (inverseInverts e hR) := (Localization.originalEquivalence
    e WC WD (forwardInverts e hL) (inverseInverts e hR)).toAdjunction
  { toFun := fun f => carrier.homEquiv X Y (α.inv.app X ≫ f) ≫ β.hom.app Y
    invFun := fun g => α.hom.app X ≫ (carrier.homEquiv X Y).symm
      (g ≫ β.inv.app Y)
    left_inv := fun f => by
      change α.hom.app X ≫ (carrier.homEquiv X Y).symm
        ((carrier.homEquiv X Y (α.inv.app X ≫ f) ≫ β.hom.app Y) ≫ β.inv.app Y) = f
      rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
        Equiv.symm_apply_apply, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    right_inv := fun g => by
      change carrier.homEquiv X Y
        (α.inv.app X ≫ (α.hom.app X ≫ (carrier.homEquiv X Y).symm
          (g ≫ β.inv.app Y))) ≫ β.hom.app Y = g
      rw [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp,
        Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] }

/-- Every actual canonical derived adjunct is the transported original carrier adjunct. -/
theorem derivedHomEquivTransport (e : C ≌ D) [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    (X : (WC).Localization) (Y : (WD).Localization)
    (f : (quillenDerivedAdjunctionData e.toAdjunction).leftDerived.obj X ⟶ Y) :
    (quillenDerivedAdjunctionData e.toAdjunction).adjunction.homEquiv X Y f =
      (Localization.originalEquivalence e WC WD (forwardInverts e hL) (inverseInverts e
        hR)).toAdjunction.homEquiv X Y
          ((leftDerivedComparison e hL).inv.app X ≫ f) ≫
        (rightDerivedComparison e hR).hom.app Y := by
  let data := quillenDerivedAdjunctionData e.toAdjunction
  let α := leftDerivedComparison e hL
  let β := rightDerivedComparison e hR
  let carrier : Localization.originalForward e WC WD (forwardInverts e hL) ⊣
    Localization.originalInverse e WC WD (inverseInverts e hR) := (Localization.originalEquivalence
    e WC WD (forwardInverts e hL) (inverseInverts e hR)).toAdjunction
  have hu : data.adjunction.unit.app X ≫ data.rightDerived.map (α.hom.app X) =
      carrier.unit.app X ≫ β.hom.app ((Localization.originalForward e WC WD (forwardInverts e
        hL)).obj X) :=
    congr_app (unitComparison e hL hR) X
  have hn : (Localization.originalInverse e WC WD (inverseInverts e hR)).map (α.inv.app X ≫ f) ≫
    β.hom.app Y =
      β.hom.app ((Localization.originalForward e WC WD (forwardInverts e hL)).obj X) ≫
        data.rightDerived.map (α.inv.app X ≫ f) :=
    β.hom.naturality (α.inv.app X ≫ f)
  have hf : α.hom.app X ≫ (α.inv.app X ≫ f) = f := by
    rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have hm : data.rightDerived.map (α.hom.app X) ≫
      data.rightDerived.map (α.inv.app X ≫ f) = data.rightDerived.map f :=
    (data.rightDerived.map_comp _ _).symm.trans
      (congrArg (fun g => data.rightDerived.map g) hf)
  change data.adjunction.homEquiv X Y f =
    carrier.homEquiv X Y (α.inv.app X ≫ f) ≫ β.hom.app Y
  symm
  calc
    carrier.homEquiv X Y (α.inv.app X ≫ f) ≫ β.hom.app Y =
        (carrier.unit.app X ≫ (Localization.originalInverse e WC WD (inverseInverts e hR)).map
          (α.inv.app X ≫ f)) ≫ β.hom.app Y :=
      congrArg (fun g => g ≫ β.hom.app Y) (carrier.homEquiv_unit X Y (α.inv.app X ≫ f))
    _ = carrier.unit.app X ≫
        ((Localization.originalInverse e WC WD (inverseInverts e hR)).map (α.inv.app X ≫ f) ≫
          β.hom.app Y) := Category.assoc _ _ _
    _ = carrier.unit.app X ≫
        (β.hom.app ((Localization.originalForward e WC WD (forwardInverts e hL)).obj X) ≫
          data.rightDerived.map (α.inv.app X ≫ f)) :=
      congrArg (fun g => carrier.unit.app X ≫ g) hn
    _ = (carrier.unit.app X ≫ β.hom.app ((Localization.originalForward e WC WD (forwardInverts e
      hL)).obj X)) ≫
        data.rightDerived.map (α.inv.app X ≫ f) := (Category.assoc _ _ _).symm
    _ = (data.adjunction.unit.app X ≫ data.rightDerived.map (α.hom.app X)) ≫
        data.rightDerived.map (α.inv.app X ≫ f) :=
      congrArg (fun g => g ≫ data.rightDerived.map (α.inv.app X ≫ f)) hu.symm
    _ = data.adjunction.unit.app X ≫
        (data.rightDerived.map (α.hom.app X) ≫ data.rightDerived.map (α.inv.app X ≫ f)) :=
      Category.assoc _ _ _
    _ = data.adjunction.unit.app X ≫ data.rightDerived.map f :=
      congrArg (fun g => data.adjunction.unit.app X ≫ g) hm
    _ = data.adjunction.homEquiv X Y f := (data.adjunction.homEquiv_unit X Y f).symm

/-- Equality of the complete original canonical and transported carrier Hom equivalences. -/
theorem derivedHomEquiv_eq (e : C ≌ D) [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    (X : (WC).Localization) (Y : (WD).Localization) :
    (quillenDerivedAdjunctionData e.toAdjunction).adjunction.homEquiv X Y =
      transportedHomEquiv e hL hR X Y := by
  apply Equiv.ext
  intro f
  exact derivedHomEquivTransport e hL hR X Y f

/-- The whole forward Hom function retains the actual original carrier and comparisons. -/
theorem derivedHomFunction_eq (e : C ≌ D) [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    (X : (WC).Localization) (Y : (WD).Localization) :
    ((quillenDerivedAdjunctionData e.toAdjunction).adjunction.homEquiv X Y).toFun =
      (transportedHomEquiv e hL hR X Y).toFun :=
  congrArg Equiv.toFun (derivedHomEquiv_eq e hL hR X Y)

/-- The whole inverse Hom function keeps the same actual inverse comparison maps. -/
theorem derivedHomInverseFunction_eq (e : C ≌ D)
    [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    (X : (WC).Localization) (Y : (WD).Localization) :
    ((quillenDerivedAdjunctionData e.toAdjunction).adjunction.homEquiv X Y).invFun =
      (transportedHomEquiv e hL hR X Y).invFun :=
  congrArg Equiv.invFun (derivedHomEquiv_eq e hL hR X Y)

/-- Every actual inverse canonical adjunct is the complete transported carrier inverse. -/
theorem derivedHomEquivInverseTransport (e : C ≌ D)
    [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    (X : (WC).Localization) (Y : (WD).Localization)
    (g : X ⟶ (quillenDerivedAdjunctionData e.toAdjunction).rightDerived.obj Y) :
    ((quillenDerivedAdjunctionData e.toAdjunction).adjunction.homEquiv X Y).symm g =
      (leftDerivedComparison e hL).hom.app X ≫
        ((Localization.originalEquivalence e WC WD (forwardInverts e hL) (inverseInverts e
          hR)).toAdjunction.homEquiv X Y).symm
          (g ≫ (rightDerivedComparison e hR).inv.app Y) :=
  congrFun (derivedHomInverseFunction_eq e hL hR X Y) g

/-- The full transported adjunct function is natural in every localized source arrow. -/
theorem transportedHomLeftNaturality (e : C ≌ D)
    [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    {X X' : (WC).Localization} {Y : (WD).Localization}
    (f : X' ⟶ X) (g : (quillenDerivedAdjunctionData e.toAdjunction).leftDerived.obj X ⟶ Y) :
    transportedHomEquiv e hL hR X' Y
        ((quillenDerivedAdjunctionData e.toAdjunction).leftDerived.map f ≫ g) =
      f ≫ transportedHomEquiv e hL hR X Y g := by
  rw [← derivedHomEquiv_eq e hL hR X' Y, ← derivedHomEquiv_eq e hL hR X Y]
  exact (quillenDerivedAdjunctionData e.toAdjunction).adjunction.homEquiv_naturality_left f g

/-- The whole transported adjunct function is natural in every localized target arrow. -/
theorem transportedHomRightNaturality (e : C ≌ D)
    [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    {X : (WC).Localization} {Y Y' : (WD).Localization}
    (f : (quillenDerivedAdjunctionData e.toAdjunction).leftDerived.obj X ⟶ Y) (g : Y ⟶ Y') :
    transportedHomEquiv e hL hR X Y' (f ≫ g) =
      transportedHomEquiv e hL hR X Y f ≫
        (quillenDerivedAdjunctionData e.toAdjunction).rightDerived.map g := by
  rw [← derivedHomEquiv_eq e hL hR X Y', ← derivedHomEquiv_eq e hL hR X Y]
  exact (quillenDerivedAdjunctionData e.toAdjunction).adjunction.homEquiv_naturality_right f g

/-- The full inverse transported Hom function is natural in every localized source arrow. -/
theorem transportedHomInverseLeftNaturality (e : C ≌ D)
    [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    {X X' : (WC).Localization} {Y : (WD).Localization}
    (f : X' ⟶ X) (g : X ⟶ (quillenDerivedAdjunctionData e.toAdjunction).rightDerived.obj Y) :
    (transportedHomEquiv e hL hR X' Y).symm (f ≫ g) =
      (quillenDerivedAdjunctionData e.toAdjunction).leftDerived.map f ≫
        (transportedHomEquiv e hL hR X Y).symm g := by
  rw [← derivedHomEquiv_eq e hL hR X' Y, ← derivedHomEquiv_eq e hL hR X Y]
  exact (quillenDerivedAdjunctionData e.toAdjunction).adjunction.homEquiv_naturality_left_symm f g

/-- The complete inverse transported Hom function is natural in every localized target arrow. -/
theorem transportedHomInverseRightNaturality (e : C ≌ D)
    [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse)
    {X : (WC).Localization} {Y Y' : (WD).Localization}
    (f : X ⟶ (quillenDerivedAdjunctionData e.toAdjunction).rightDerived.obj Y) (g : Y ⟶ Y') :
    (transportedHomEquiv e hL hR X Y').symm
        (f ≫ (quillenDerivedAdjunctionData e.toAdjunction).rightDerived.map g) =
      (transportedHomEquiv e hL hR X Y).symm f ≫ g := by
  rw [← derivedHomEquiv_eq e hL hR X Y', ← derivedHomEquiv_eq e hL hR X Y]
  exact (quillenDerivedAdjunctionData e.toAdjunction).adjunction.homEquiv_naturality_right_symm f g

/-- The complete transported Hom function recovers the same original canonical unit. -/
theorem transportedHomUnit (e : C ≌ D) [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse) (X : (WC).Localization) :
    transportedHomEquiv e hL hR X
        ((quillenDerivedAdjunctionData e.toAdjunction).leftDerived.obj X) (𝟙 _) =
      (quillenDerivedAdjunctionData e.toAdjunction).adjunction.unit.app X := by
  rw [← derivedHomEquiv_eq]
  exact (quillenDerivedAdjunctionData e.toAdjunction).adjunction.homEquiv_id X

/-- The complete inverse transported Hom function recovers the actual canonical counit. -/
theorem transportedHomCounit (e : C ≌ D) [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse) (Y : (WD).Localization) :
    (transportedHomEquiv e hL hR
        ((quillenDerivedAdjunctionData e.toAdjunction).rightDerived.obj Y) Y).symm (𝟙 _) =
      (quillenDerivedAdjunctionData e.toAdjunction).adjunction.counit.app Y := by
  rw [← derivedHomEquiv_eq]
  exact (quillenDerivedAdjunctionData e.toAdjunction).adjunction.homEquiv_symm_id Y

/-- The whole transported unit and counit satisfy the actual left triangle on all objects. -/
theorem transportedHomLeftTriangle (e : C ≌ D)
    [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse) (X : (WC).Localization) :
    (quillenDerivedAdjunctionData e.toAdjunction).leftDerived.map
        (transportedHomEquiv e hL hR X
          ((quillenDerivedAdjunctionData e.toAdjunction).leftDerived.obj X) (𝟙 _)) ≫
      (transportedHomEquiv e hL hR
          ((quillenDerivedAdjunctionData e.toAdjunction).rightDerived.obj
            ((quillenDerivedAdjunctionData e.toAdjunction).leftDerived.obj X))
          ((quillenDerivedAdjunctionData e.toAdjunction).leftDerived.obj X)).symm (𝟙 _) =
        𝟙 ((quillenDerivedAdjunctionData e.toAdjunction).leftDerived.obj X) := by
  rw [transportedHomUnit, transportedHomCounit]
  exact (quillenDerivedAdjunctionData e.toAdjunction).adjunction.left_triangle_components X

/-- The entire transported unit and counit satisfy the actual right triangle on all objects. -/
theorem transportedHomRightTriangle (e : C ≌ D)
    [Adjunction.IsQuillenAdjunction e.toAdjunction]
    (hL : WC ≤ (WD).inverseImage e.functor)
    (hR : WD ≤ (WC).inverseImage e.inverse) (Y : (WD).Localization) :
    transportedHomEquiv e hL hR
        ((quillenDerivedAdjunctionData e.toAdjunction).rightDerived.obj Y)
        ((quillenDerivedAdjunctionData e.toAdjunction).leftDerived.obj
          ((quillenDerivedAdjunctionData e.toAdjunction).rightDerived.obj Y)) (𝟙 _) ≫
      (quillenDerivedAdjunctionData e.toAdjunction).rightDerived.map
        ((transportedHomEquiv e hL hR
            ((quillenDerivedAdjunctionData e.toAdjunction).rightDerived.obj Y) Y).symm (𝟙 _)) =
          𝟙 ((quillenDerivedAdjunctionData e.toAdjunction).rightDerived.obj Y) := by
  rw [transportedHomUnit, transportedHomCounit]
  exact (quillenDerivedAdjunctionData e.toAdjunction).adjunction.right_triangle_components Y

end HomotopicalAlgebra.QuillenCarrierLocalization
