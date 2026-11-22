/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.Basic

/-!
# Derived sphere and permutation actions on native symmetric spectra

The complete source sphere-module structures are recovered from the full native
operator action. These accessors retain both tensor orders, every finite index
and every coefficient label. Their laws are consequences of the actual
reconstruction, including the original sphere tensorator and block braids.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed CategoryTheory.MonObj ExternalProduct

namespace PointedCGWH.SymmetricSpectrum

private abbrev I := Operad.SmallFinBijGroupoid
private abbrev V := PointedCGWH.{u, v}

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

/-- The complete original coefficient-first sphere action. -/
abbrev leftPairAction (F : SymmetricSpectrum.{u, v}) (a n : I) :
    sphereSequence.{u, v}.functor.obj a ⊗ F.X.functor.obj n ⟶ F.X.functor.obj (a ⊗ n) :=
  SymmetricModulePresentation.reconstructedPairAction F a n

/-- The full coefficient-first action followed by any original target label. -/
abbrev leftArrowAction (F : SymmetricSpectrum.{u, v}) (a n k : I) (f : a ⊗ n ⟶ k) :
    sphereSequence.{u, v}.functor.obj a ⊗ F.X.functor.obj n ⟶ F.X.functor.obj k :=
  SymmetricModulePresentation.reconstructedArrowAction F a n k f

/-- The entire curried action is the original coend generator followed by the native Hom map. -/
abbrev curriedArrowAction (F : SymmetricSpectrum.{u, v}) (a n k : I) (f : a ⊗ n ⟶ k) :
    sphereSequence.{u, v}.functor.obj a ⟶
      (ihom (F.X.functor.obj n)).obj (F.X.functor.obj k) :=
  SymmetricModulePresentation.reconstructedCurriedAction F a n k f

/-- The right sphere-module presentation uses the proved braided conversion. -/
def toRightModule : SymmetricSpectrum.{u, v} ⥤
    SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
  SymmetricRightModulePresentation.operatorToRightModule.{u, v}

/-- The right source carrier acts on each entire native operator Hom. -/
def ofRightModule : SymmetricRightModulePresentation.RightSphereModule.{u, v} ⥤
    SymmetricSpectrum.{u, v} :=
  SymmetricRightModulePresentation.rightModuleToOperator.{u, v}

/-- The right presentation retains the identical underlying symmetric sequence. -/
theorem toRightModule_X (F : SymmetricSpectrum.{u, v}) :
    (toRightModule.obj F).X = F.X := rfl

/-- Every original right-module source map retains the complete native sequence map. -/
theorem toRightModule_hom {F G : SymmetricSpectrum.{u, v}} (f : F ⟶ G) :
    (toRightModule.map f).hom = hom f := by
  change (CommutativeModuleConversion.toRightMap sphereSequence.{u, v}
    (SymmetricModulePresentation.reconstructedModuleMap f)).hom = _
  rw [CommutativeModuleConversion.toRightMap_hom]
  rfl

/-- The actual coefficient-right pair action in the reconstructed source module. -/
abbrev rightPairAction (F : SymmetricSpectrum.{u, v}) (n a : I) :
    F.X.functor.obj n ⊗ sphereSequence.{u, v}.functor.obj a ⟶ F.X.functor.obj (n ⊗ a) :=
  SymmetricRightModulePresentation.pairAction (toRightModule.obj F) n a

/-- The full right source arrow includes its unchanged original target permutation. -/
abbrev rightArrowAction (F : SymmetricSpectrum.{u, v}) (n a k : I) (f : n ⊗ a ⟶ k) :
    F.X.functor.obj n ⊗ sphereSequence.{u, v}.functor.obj a ⟶ F.X.functor.obj k :=
  SymmetricRightModulePresentation.arrowAction (toRightModule.obj F) n a k f

/-- The original left module pair action is the same complete native action. -/
theorem toModule_pairAction (F : SymmetricSpectrum.{u, v}) (a n : I) :
    SymmetricModulePresentation.pairAction (toModule.obj F) a n = leftPairAction F a n :=
  SymmetricModulePresentation.reconstructedModule_pairAction F a n

/-- The original left module label action is recovered without projecting the Hom coend. -/
theorem toModule_arrowAction (F : SymmetricSpectrum.{u, v}) (a n k : I) (f : a ⊗ n ⟶ k) :
    SymmetricModulePresentation.arrowAction (toModule.obj F) a n k f = leftArrowAction F a n k f :=
  SymmetricModulePresentation.reconstructedModule_arrowAction F a n k f

/-- Every native Hom map is recovered from the actual source module, on the whole Hom object. -/
theorem toModule_fullHom (F : SymmetricSpectrum.{u, v}) (n k : I) :
    SymmetricModulePresentation.operatorHomMap (toModule.obj F) n k =
      F.toEnrichedFunctor.map (symmetricOperatorObj.{u, v} n) (symmetricOperatorObj.{u, v} k) :=
  SymmetricModulePresentation.operatorHomMap_reconstructed F n k

/-- The original left-labelled action has the same complete closed transpose. -/
theorem toModule_curriedAction (F : SymmetricSpectrum.{u, v}) (a n k : I) (f : a ⊗ n ⟶ k) :
    SymmetricModulePresentation.curriedArrowAction (toModule.obj F) a n k f =
      curriedArrowAction F a n k f :=
  SymmetricModulePresentation.reconstructedModule_curriedAction F a n k f

/-- Both actual index maps act naturally on the complete coefficient-first pair. -/
theorem leftPairAction_naturality (F : SymmetricSpectrum.{u, v})
    {a a' n n' : I} (r : a ⟶ a') (g : n ⟶ n') :
    (sphereSequence.{u, v}.functor.map r ⊗ₘ F.X.functor.map g) ≫
        leftPairAction F a' n' = leftPairAction F a n ≫ F.X.functor.map (r ⊗ₘ g) :=
  SymmetricModulePresentation.reconstructedPairAction_naturality F r g

/-- Both original right index maps retain their full pair naturality square. -/
theorem rightPairAction_naturality (F : SymmetricSpectrum.{u, v})
    {n n' a a' : I} (f : n ⟶ n') (g : a ⟶ a') :
    (F.X.functor.map f ⊗ₘ sphereSequence.{u, v}.functor.map g) ≫
        rightPairAction F n' a' = rightPairAction F n a ≫ F.X.functor.map (f ⊗ₘ g) :=
  SymmetricRightModulePresentation.pairAction_naturality (toRightModule.obj F) f g

/-- Every source coefficient relation is retained before and after the whole Hom map. -/
theorem curriedArrowAction_coefficient (F : SymmetricSpectrum.{u, v})
    {a b : I} (r : a ⟶ b) (n k : I) (f : b ⊗ n ⟶ k) :
    sphereSequence.{u, v}.functor.map r ≫ curriedArrowAction F b n k f =
      curriedArrowAction F a n k ((r ⊗ₘ 𝟙 n) ≫ f) :=
  SymmetricModulePresentation.reconstructedCurriedAction_coefficient F r n k f

/-- The native left action retains every original target-index label. -/
theorem leftArrowAction_target (F : SymmetricSpectrum.{u, v}) (a n k l : I)
    (f : a ⊗ n ⟶ k) (g : k ⟶ l) :
    leftArrowAction F a n k f ≫ F.X.functor.map g = leftArrowAction F a n l (f ≫ g) :=
  SymmetricModulePresentation.reconstructedArrowAction_target F a n k l f g

/-- The native coefficient unit is the actual original level identity. -/
theorem leftArrowAction_unit (F : SymmetricSpectrum.{u, v}) (n : I) :
    (sphereCopowerLaxData.{u, v}.epsilon ▷ F.X.functor.obj n) ≫
      leftArrowAction F (𝟙_ I) n n (λ_ n).hom = (λ_ (F.X.functor.obj n)).hom :=
  SymmetricModulePresentation.reconstructedArrowAction_unit F n

/-- The complete two-label action retains the original late-first multiplication and associator. -/
theorem leftArrowAction_comp (F : SymmetricSpectrum.{u, v}) (a b n k l : I)
    (f : a ⊗ n ⟶ k) (g : b ⊗ k ⟶ l) :
    (sphereCopowerLaxData.{u, v}.mu
        ((copowerRestriction.{u, v, 0} I).obj b)
        ((copowerRestriction.{u, v, 0} I).obj a) ▷ F.X.functor.obj n) ≫
      leftArrowAction F (b ⊗ a) n l ((α_ b a n).hom ≫ (𝟙 b ⊗ₘ f) ≫ g) =
    (α_ (sphereSequence.{u, v}.functor.obj b) (sphereSequence.{u, v}.functor.obj a)
      (F.X.functor.obj n)).hom ≫
      (sphereSequence.{u, v}.functor.obj b ◁ leftArrowAction F a n k f) ≫
        leftArrowAction F b k l g :=
  SymmetricModulePresentation.reconstructedArrowAction_comp F a b n k l f g

/-- Every native spectrum map intertwines both entire original left sphere actions. -/
theorem leftPairAction_morphism {F G : SymmetricSpectrum.{u, v}} (f : F ⟶ G) (a n : I) :
    leftPairAction F a n ≫ (hom f).natTrans.app (a ⊗ n) =
      (sphereSequence.{u, v}.functor.obj a ◁ (hom f).natTrans.app n) ≫ leftPairAction G a n :=
  SymmetricModulePresentation.reconstructedPairAction_morphism f a n

/-- Every complete native spectrum map retains every original left target label. -/
theorem leftArrowAction_morphism {F G : SymmetricSpectrum.{u, v}} (f : F ⟶ G)
    (a n k : I) (g : a ⊗ n ⟶ k) :
    leftArrowAction F a n k g ≫ (hom f).natTrans.app k =
      (sphereSequence.{u, v}.functor.obj a ◁ (hom f).natTrans.app n) ≫
        leftArrowAction G a n k g := by
  rw [hom_app, hom_app]
  exact SymmetricModulePresentation.reconstructedArrowAction_morphism f a n k g

/-- The actual native left and right action formulas keep both the value braid and index braid. -/
theorem rightPairAction_formula (F : SymmetricSpectrum.{u, v}) (n a : I) :
    rightPairAction F n a =
      (β_ (F.X.functor.obj n) (sphereSequence.{u, v}.functor.obj a)).hom ≫
        leftPairAction F a n ≫ F.X.functor.map (β_ a n).hom := by
  let M := toModule.obj F
  let s : sphereSequence.{u, v} ⊗ M.X ⟶ M.X :=
    ModObj.smul (M := sphereSequence.{u, v}) (X := M.X)
  have hB := SymmetricRightModulePresentation.dayBraiding_generator M.X sphereSequence.{u, v} n a
  have hN := s.natTrans.naturality (β_ a n).hom
  change (DayFunctor.η M.X sphereSequence.{u, v}).app (n, a) ≫
    (CommutativeModuleConversion.rightAction sphereSequence.{u, v} M).natTrans.app (n ⊗ a) = _
  dsimp only [CommutativeModuleConversion.rightAction]
  change (DayFunctor.η M.X sphereSequence.{u, v}).app (n, a) ≫
    (β_ M.X sphereSequence.{u, v}).hom.natTrans.app (n ⊗ a) ≫
      s.natTrans.app (n ⊗ a) = _
  rw [← Category.assoc, hB]
  simp only [Category.assoc]
  rw [hN]
  change _ = (β_ (F.X.functor.obj n) (sphereSequence.{u, v}.functor.obj a)).hom ≫
    leftPairAction F a n ≫ F.X.functor.map (β_ a n).hom
  rw [← toModule_pairAction]
  rfl

/-- The source right-labelled action retains its entire target map. -/
theorem rightArrowAction_formula (F : SymmetricSpectrum.{u, v}) (n a k : I)
    (f : n ⊗ a ⟶ k) :
    rightArrowAction F n a k f =
      (β_ (F.X.functor.obj n) (sphereSequence.{u, v}.functor.obj a)).hom ≫
        leftArrowAction F a n k ((β_ a n).hom ≫ f) := by
  change rightPairAction F n a ≫ F.X.functor.map f = _
  rw [rightPairAction_formula]
  simp only [Category.assoc]
  rw [← F.X.functor.map_comp]
  change (β_ (F.X.functor.obj n) (sphereSequence.{u, v}.functor.obj a)).hom ≫
    leftArrowAction F a n (a ⊗ n) (𝟙 (a ⊗ n)) ≫
      F.X.functor.map ((β_ a n).hom ≫ f) = _
  rw [leftArrowAction_target, Category.id_comp]

end PointedCGWH.SymmetricSpectrum
