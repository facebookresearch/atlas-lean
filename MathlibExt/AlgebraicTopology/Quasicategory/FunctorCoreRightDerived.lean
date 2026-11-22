/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.FunctorCoreHomotopyInvariance
import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalModelCategory
import Mathlib.AlgebraicTopology.ModelCategory.DerivabilityStructureFibrant
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-!
# The actual right-derived functor-core mapping row

The original functor core is retained before localizing in Kan. Its
homotopy invariance on genuine fibrant Joyal objects proves derivability
through the native fibrant-object structure. The canonical derived unit
is therefore an Iso at every original quasicategory target. Source maps
are derived from their original core-precomposition transformations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped JoyalSSet.ModelCategory

namespace SSet.FunctorCore.RightDerived

variable {E : Type w} [Category.{v} E]
  (L : SSet.{u} ⥤ E) [L.IsLocalization realizationWeakEquivalences.{u}]

/-- The SAME raw full functor core, followed by the actual scalar localization. -/
def raw (A : SSet.{u}) : JoyalSSet.{u} ⥤ E :=
  JoyalSSet.forget ⋙ FunctorCore.functor A ⋙ L

/-- The original source map acts on the whole localized raw mapping row. -/
def rawSource {A B : SSet.{u}} (a : A ⟶ B) : raw L B ⟶ raw L A :=
  Functor.whiskerLeft JoyalSSet.forget (Functor.whiskerRight (FunctorCore.sourceMap a) L)

omit [L.IsLocalization realizationWeakEquivalences.{u}] in
/-- Every actual component is scalar localization of the SAME original core precomposition. -/
theorem rawSource_app {A B : SSet.{u}} (a : A ⟶ B) (X : JoyalSSet.{u}) :
    (rawSource L a).app X = L.map ((FunctorCore.sourceMap a).app X.toSSet) := rfl

/-- Genuine categorical equivalences on fibrant targets make this native row derivable. -/
theorem derives (A : SSet.{u}) :
    (FibrantObject.localizerMorphism JoyalSSet.{u}).Derives (raw L A) := by
  intro X Y f hf
  let _ : Quasicategory (JoyalSSet.forget.obj X.obj) :=
    (JoyalSSet.isFibrant_iff_quasicategory X.obj).mp
    (inferInstance : IsFibrant X.obj)
  let _ : Quasicategory (JoyalSSet.forget.obj Y.obj) :=
    (JoyalSSet.isFibrant_iff_quasicategory Y.obj).mp
    (inferInstance : IsFibrant Y.obj)
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences f.hom at hf
  rw [JoyalSSet.modelCategory_weakEquivalences] at hf
  change categoricalEquivalences (JoyalSSet.forget.map f.hom) at hf
  let _ : KanComplex ((FunctorCore.functor A).obj (JoyalSSet.forget.obj X.obj)) :=
    FunctorCore.isKan A _
  let _ : KanComplex ((FunctorCore.functor A).obj (JoyalSSet.forget.obj Y.obj)) :=
    FunctorCore.isKan A _
  have hw := (KanComplex.W_iff_realizationWeakEquivalence _).mp
    (FunctorCore.map_weak (JoyalSSet.forget.map f.hom) hf A)
  exact Localization.inverts L realizationWeakEquivalences _ hw

instance hasPointwiseRightDerived (A : SSet.{u}) :
    (raw L A).HasPointwiseRightDerivedFunctor (weakEquivalences JoyalSSet.{u}) :=
  (derives L A).hasPointwiseRightDerivedFunctor

/-- Use the actual localization of the SAME named Joyal weak class. -/
abbrev joyalLocalization : JoyalSSet.{u} ⥤ (weakEquivalences JoyalSSet.{u}).Localization :=
  (weakEquivalences JoyalSSet.{u}).Q

/-- The total right-derived row exists by the proved native derivability structure. -/
def row (A : SSet.{u}) : (weakEquivalences JoyalSSet.{u}).Localization ⥤ E :=
  (raw L A).totalRightDerived joyalLocalization (weakEquivalences JoyalSSet.{u})

/-- Its comparison is the SAME total-right-derived unit, with no supplied Iso premise. -/
def unit (A : SSet.{u}) : raw L A ⟶ joyalLocalization ⋙ row L A :=
  (raw L A).totalRightDerivedUnit joyalLocalization (weakEquivalences JoyalSSet.{u})

instance row_isRightDerived (A : SSet.{u}) :
    (row L A).IsRightDerivedFunctor (unit L A) (weakEquivalences JoyalSSet.{u}) := by
  dsimp only [row, unit]
  infer_instance

/-- Native fibrant objects compute the SAME actual right-derived mapping row. -/
instance unit_isIso_of_fibrant (A : SSet.{u}) (X : JoyalSSet.{u}) [IsFibrant X] :
    IsIso ((unit L A).app X) :=
  (derives L A).isIso_of_isRightDerivedFunctor (unit L A) (FibrantObject.mk X)

/-- A quasicategory's original functor core is identified by the canonical derived unit. -/
def nativeIso (A Q : SSet.{u}) [Quasicategory Q] :
    L.obj ((FunctorCore.functor A).obj Q) ≅
      (row L A).obj (joyalLocalization.obj (JoyalSSet.ofSSet.obj Q)) := by
  let _ : IsFibrant (JoyalSSet.ofSSet.obj Q) :=
    (JoyalSSet.isFibrant_iff_quasicategory _).mpr (inferInstance : Quasicategory Q)
  exact asIso ((unit L A).app (JoyalSSet.ofSSet.obj Q))

/-- The forward identification is the literal canonical derived unit at the original target. -/
theorem nativeIso_hom (A Q : SSet.{u}) [Quasicategory Q] :
    (nativeIso L A Q).hom = (unit L A).app (JoyalSSet.ofSSet.obj Q) := rfl

/-- Original target maps retain the whole derived-unit square. -/
theorem nativeIso_target (A : SSet.{u}) {Q Q' : SSet.{u}}
    [Quasicategory Q] [Quasicategory Q'] (f : Q ⟶ Q') :
    L.map ((FunctorCore.functor A).map f) ≫ (nativeIso L A Q').hom =
      (nativeIso L A Q).hom ≫
        (row L A).map (joyalLocalization.map (JoyalSSet.ofSSet.map f)) :=
  (unit L A).naturality (JoyalSSet.ofSSet.map f)

/-- Derive the SAME source-precomposition natural transformation. -/
def source {A B : SSet.{u}} (a : A ⟶ B) : row L B ⟶ row L A :=
  Functor.rightDerivedNatTrans (row L B) (row L A) (unit L B) (unit L A)
    (weakEquivalences JoyalSSet.{u}) (rawSource L a)

/-- The derived-source comparison retains original core precomposition and both units. -/
theorem source_unit {A B : SSet.{u}} (a : A ⟶ B) (X : JoyalSSet.{u}) :
    (unit L B).app X ≫ (source L a).app (joyalLocalization.obj X) =
      L.map ((FunctorCore.sourceMap a).app X.toSSet) ≫ (unit L A).app X :=
  Functor.rightDerivedNatTrans_app _ _ _ _ _ (rawSource L a) X

/-- The source square identifies the SAME original core mapping objects. -/
theorem nativeIso_source {A B : SSet.{u}} (a : A ⟶ B) (Q : SSet.{u}) [Quasicategory Q] :
    (nativeIso L B Q).hom ≫ (source L a).app
        (joyalLocalization.obj (JoyalSSet.ofSSet.obj Q)) =
      L.map ((FunctorCore.sourceMap a).app Q) ≫ (nativeIso L A Q).hom :=
  source_unit L a (JoyalSSet.ofSSet.obj Q)

/-- Source identities remain identities on the actual total right-derived row. -/
theorem source_id (A : SSet.{u}) : source L (𝟙 A) = 𝟙 (row L A) := by
  have h : rawSource L (𝟙 A) = 𝟙 (raw L A) := by
    apply NatTrans.ext
    funext X
    change L.map ((FunctorCore.sourceMap (𝟙 A)).app X.toSSet) = 𝟙 _
    rw [FunctorCore.sourceMap_id, NatTrans.id_app]
    exact L.map_id _
  rw [source, h]
  exact Functor.rightDerivedNatTrans_id _ _ _

/-- Actual source compositions keep the contravariant order after deriving. -/
theorem source_comp {A B C : SSet.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    source L (a ≫ b) = source L b ≫ source L a := by
  have h : rawSource L (a ≫ b) = rawSource L b ≫ rawSource L a := by
    apply NatTrans.ext
    funext X
    change L.map ((FunctorCore.sourceMap (a ≫ b)).app X.toSSet) =
      L.map ((FunctorCore.sourceMap b).app X.toSSet) ≫
        L.map ((FunctorCore.sourceMap a).app X.toSSet)
    rw [FunctorCore.sourceMap_comp, NatTrans.comp_app, Functor.map_comp]
  rw [source, h]
  exact (Functor.rightDerivedNatTrans_comp _ _ _ _ _ _ _ _ _).symm

/-- Both original mapping actions keep the SAME two canonical derived units. -/
theorem unit_joint {A B : SSet.{u}} (a : A ⟶ B) {X Y : JoyalSSet.{u}} (f : X ⟶ Y) :
    (unit L B).app X ≫ (source L a).app (joyalLocalization.obj X) ≫
        (row L A).map (joyalLocalization.map f) =
      L.map (FunctorCore.mapBoth a (JoyalSSet.forget.map f)) ≫ (unit L A).app Y := by
  have ht := (unit L A).naturality f
  change L.map ((FunctorCore.functor A).map (JoyalSSet.forget.map f)) ≫
      (unit L A).app Y = (unit L A).app X ≫
        (row L A).map (joyalLocalization.map f) at ht
  rw [← Category.assoc, source_unit, Category.assoc, ← ht, ← Category.assoc,
    ← L.map_comp]
  rfl

/-- Actual categorical equivalences of arbitrary sources induce Isos of the full derived rows. -/
theorem source_isIso {A B : SSet.{u}} (a : A ⟶ B) (ha : categoricalEquivalences a) :
    IsIso (source L a) := by
  let Φ := FibrantObject.localizerMorphism JoyalSSet.{u}
  let J := Φ.functor ⋙ joyalLocalization
  let _ : J.EssSurj := Φ.essSurj_of_hasRightResolutions joyalLocalization
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  rw [NatTrans.isIso_app_iff_of_iso (source L a) (J.objObjPreimageIso Y).symm]
  let X := J.objPreimage Y
  let _ : Quasicategory X.obj.toSSet :=
    (JoyalSSet.isFibrant_iff_quasicategory X.obj).mp (inferInstance : IsFibrant X.obj)
  let _ : IsIso (L.map ((FunctorCore.sourceMap a).app X.obj.toSSet)) :=
    Localization.inverts L realizationWeakEquivalences _
      (FunctorCore.sourceMap_realizationWeak a ha X.obj.toSSet)
  let _ : IsIso ((unit L B).app X.obj) := unit_isIso_of_fibrant L B X.obj
  let _ : IsIso ((unit L A).app X.obj) := unit_isIso_of_fibrant L A X.obj
  have hi : IsIso ((unit L B).app X.obj ≫
      (source L a).app (joyalLocalization.obj X.obj)) := by
    rw [source_unit]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp hi

end SSet.FunctorCore.RightDerived
