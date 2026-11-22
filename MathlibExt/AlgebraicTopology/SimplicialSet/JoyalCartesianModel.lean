/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalModelCategory
import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteJoyalIntervalTestingCorners
import MathlibExt.AlgebraicTopology.ModelCategory.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

/-!
# The Cartesian Joyal model

The named Joyal model has a closed symmetric Cartesian tensor. Both
trivial pushout-product orientations and the cofibrant-unit axiom use
categorical weak equivalences.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory

namespace JoyalSSet

private instance hasFiniteProducts : HasFiniteProducts JoyalSSet.{u} where
  out J := by infer_instance

/-- The ordinary Cartesian tensor on the designated simplicial-set carrier. -/
instance cartesianMonoidalCategory : CartesianMonoidalCategory JoyalSSet.{u} :=
  CartesianMonoidalCategory.ofHasFiniteProducts

/-- Cartesian closedness is inherited through the original ordinary equivalence. -/
instance monoidalClosed : MonoidalClosed JoyalSSet.{u} :=
  cartesianClosedOfEquiv equivalenceSSet.{u}.symm

/-- The ordinary braiding is the native Cartesian product swap. -/
instance braidedCategory : BraidedCategory JoyalSSet.{u} :=
  BraidedCategory.ofCartesianMonoidalCategory

private def tensorForget : JoyalSSet.{u} ⥤ JoyalSSet.{u} ⥤ SSet.{u} :=
  curriedTensor JoyalSSet.{u} ⋙
    (Functor.whiskeringRight JoyalSSet.{u} JoyalSSet.{u} SSet.{u}).obj forget

private def forgetTensor : JoyalSSet.{u} ⥤ JoyalSSet.{u} ⥤ SSet.{u} :=
  forget ⋙ curriedTensor SSet.{u} ⋙
    (Functor.whiskeringLeft JoyalSSet.{u} SSet.{u} SSet.{u}).obj forget

private def tensorForgetIso : tensorForget.{u} ≅ forgetTensor.{u} :=
  CartesianMonoidalCategory.prodComparisonBifunctorNatIso forget.{u}

/-- Forget the original Cartesian pushout-product square and compare it with the
chosen simplicial-set square, retaining both source and target maps. -/
private def forgetPushoutProductIso {A B K L : JoyalSSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) :
    Arrow.mk (forget.map (Arrow.mk i □ Arrow.mk j).hom) ≅
      Arrow.mk (Arrow.mk (forget.map i) □ Arrow.mk (forget.map j)).hom := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor JoyalSSet.{u}) i j
  let mapped : tensorForget.PushoutObjObj i j :=
    { pt := forget.obj sq.pt
      inl := forget.map sq.inl
      inr := forget.map sq.inr
      isPushout := sq.isPushout.map forget
      ι := forget.map sq.ι
      inl_ι := (forget.map_comp sq.inl sq.ι).symm.trans
        (congrArg (fun f => forget.map f) sq.inl_ι)
      inr_ι := (forget.map_comp sq.inr sq.ι).symm.trans
        (congrArg (fun f => forget.map f) sq.inr_ι) }
  let compared := mapped.ofNatIso tensorForgetIso
  let raw : (curriedTensor SSet.{u}).PushoutObjObj (forget.map i) (forget.map j) :=
    { pt := compared.pt
      inl := compared.inl
      inr := compared.inr
      isPushout := compared.isPushout
      ι := compared.ι
      inl_ι := compared.inl_ι
      inr_ι := compared.inr_ι }
  refine Arrow.isoMk raw.isPushout.isoPushout
    (CartesianMonoidalCategory.prodComparisonIso forget B L) ?_
  change raw.isPushout.isoPushout.hom ≫
      (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u})
        (forget.map i) (forget.map j)).ι = raw.ι
  apply raw.hom_ext
  · simp
  · simp

attribute [local instance] modelCategory

private theorem cofibration_iff_mono {A B : JoyalSSet.{u}} (f : A ⟶ B) :
    cofibrations JoyalSSet.{u} f ↔ Mono f := by
  change modelCategory.categoryWithCofibrations.cofibrations f ↔ Mono f
  rw [modelCategory_cofibrations]

private theorem trivialCofibration_iff {A B : JoyalSSet.{u}} (f : A ⟶ B) :
    trivialCofibrations JoyalSSet.{u} f ↔
      Mono f ∧ SSet.categoricalEquivalences (forget.map f) := by
  change (cofibrations JoyalSSet.{u} f ∧ weakEquivalences JoyalSSet.{u} f) ↔ _
  rw [cofibration_iff_mono]
  change (Mono f ∧ modelCategory.categoryWithWeakEquivalences.weakEquivalences f) ↔ _
  rw [modelCategory_weakEquivalences]
  rfl

private theorem cofibration_pushoutProduct {A B K L : JoyalSSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L)
    (hi : cofibrations JoyalSSet.{u} i) (hj : cofibrations JoyalSSet.{u} j) :
    cofibrations JoyalSSet.{u} (Arrow.mk i □ Arrow.mk j).hom := by
  let _ : Mono i := (cofibration_iff_mono i).mp hi
  let _ : Mono j := (cofibration_iff_mono j).mp hj
  have hraw : monomorphisms SSet.{u}
      (Arrow.mk (forget.map i) □ Arrow.mk (forget.map j)).hom :=
    (SSet.monomorphism_product_corner (forget.map i) (forget.map j)).1
  have hf : Mono (forget.map (Arrow.mk i □ Arrow.mk j).hom) :=
    ((monomorphisms SSet.{u}).arrow_mk_iso_iff (forgetPushoutProductIso i j)).mpr hraw
  exact (cofibration_iff_mono _).mpr (forget.mono_of_mono_map hf)

private theorem trivial_pushoutProduct {A B K L : JoyalSSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) [Mono i] [Mono j]
    (hw : SSet.categoricalEquivalences (forget.map i) ∨
      SSet.categoricalEquivalences (forget.map j)) :
    trivialCofibrations JoyalSSet.{u} (Arrow.mk i □ Arrow.mk j).hom := by
  have htesting :
      SSet.joyalInterval.productPrecylinder.testingEquivalences
          SSet.joyalInterval.auxiliaryAnodyneExtensions (forget.map i) ∨
        SSet.joyalInterval.productPrecylinder.testingEquivalences
          SSet.joyalInterval.auxiliaryAnodyneExtensions (forget.map j) := by
    simpa only [SSet.joyalInterval.testingEquivalences_eq_categoricalEquivalences] using hw
  have hrawTesting := SSet.joyalInterval.testingTrivialCofibrations_pushoutProduct
    (forget.map i) (forget.map j) htesting
  have hraw : (monomorphisms SSet.{u} ⊓ SSet.categoricalEquivalences)
      (Arrow.mk (forget.map i) □ Arrow.mk (forget.map j)).hom := by
    change Mono (Arrow.mk (forget.map i) □ Arrow.mk (forget.map j)).hom ∧
      SSet.categoricalEquivalences (Arrow.mk (forget.map i) □ Arrow.mk (forget.map j)).hom
    simpa only [SSet.joyalInterval.productPrecylinder.testingTrivialCofibrations_iff,
      SSet.joyalInterval.testingEquivalences_eq_categoricalEquivalences] using hrawTesting
  have hf := ((monomorphisms SSet.{u} ⊓ SSet.categoricalEquivalences).arrow_mk_iso_iff
    (forgetPushoutProductIso i j)).mpr hraw
  exact (trivialCofibration_iff _).mpr ⟨forget.mono_of_mono_map hf.1, hf.2⟩

/-- The actual Cartesian unit is cofibrant in the named Joyal model. -/
theorem tensorUnit_isCofibrant :
    letI : ModelCategory JoyalSSet.{u} := modelCategory
    IsCofibrant (𝟙_ JoyalSSet.{u}) := by
  rw [isCofibrant_iff_of_isInitial (initial.to (𝟙_ JoyalSSet.{u})) initialIsInitial,
    HomotopicalAlgebra.cofibration_iff, cofibration_iff_mono]
  infer_instance

/-- The actual named Joyal model is closed symmetric monoidal for its Cartesian tensor. -/
theorem isClosedSymmetricMonoidalModelCategory :
    letI : ModelCategory JoyalSSet.{u} := modelCategory
    IsClosedSymmetricMonoidalModelCategory JoyalSSet.{u} := by
  let _ : IsCofibrant (𝟙_ JoyalSSet.{u}) := tensorUnit_isCofibrant
  apply isClosedSymmetricMonoidalModelCategory_of_isCofibrant_tensorUnit JoyalSSet.{u}
  · exact cofibration_pushoutProduct
  · intro A B K L i j hi hj
    obtain ⟨hmi, hwi⟩ := (trivialCofibration_iff i).mp hi
    let _ : Mono i := hmi
    let _ : Mono j := (cofibration_iff_mono j).mp hj
    exact trivial_pushoutProduct i j (Or.inl hwi)
  · intro A B K L i j hi hj
    obtain ⟨hmj, hwj⟩ := (trivialCofibration_iff j).mp hj
    let _ : Mono i := (cofibration_iff_mono i).mp hi
    let _ : Mono j := hmj
    exact trivial_pushoutProduct i j (Or.inr hwj)

end JoyalSSet
