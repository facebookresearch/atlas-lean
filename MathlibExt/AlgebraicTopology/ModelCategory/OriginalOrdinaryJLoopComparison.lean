/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OriginalGoodPathFiberGeometry
import MathlibExt.AlgebraicTopology.ModelCategory.OriginalOrdinaryCovariantPuppeConnection
import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction
import MathlibExt.AlgebraicTopology.ModelCategory.DerivedSuspensionLoopAdjunction

/-!
# Original J loops and the derived ordinary Puppe connecting map

The same fixed-κ J factory acts on the entire based good-path projection.
Its natural map from the original zero-source factorization is weak by the
original insertions. The two resulting fibre maps are weak by the cofibrant
cube in the opposite model category, using the actual fibrations and fibrant
targets. This constructs the full comparison of the original J loop carrier
with the supplied good path's two-end fibre.

The original framing specializes that comparison to the actual derived
ordinary loop object, with the original R replacement retained. The caller's
zero is compared with the framing's chosen zero by its actual isomorphism.
The original covariant Puppe boundary therefore becomes a connecting map
from the derived ordinary loops into the same caller-selected ordinary fibre.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe w u v
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped ZeroObject

namespace HomotopicalAlgebra.OriginalOrdinaryJLoopComparison

variable {C : Type u} [Category.{v} C] [ModelCategory C]

private theorem op_isCofibrant (X : C) [IsFibrant X] : IsCofibrant (op X) := by
  apply (isCofibrant_iff_of_isInitial (terminal.from X).op terminalIsTerminal.op).mpr
  exact (cofibration_op_iff _).mpr inferInstance

section FiberMaps

variable (Z : C) (hZ : IsZero Z)

/-- The full actual fibre map between two supplied projections over the same original target. -/
def fiberMap {A B Y : C} (p : A ⟶ Y) (q : B ⟶ Y) (f : A ⟶ B) (hf : f ≫ q = p) :
    pullback p (hZ.isInitial.to Y) ⟶ pullback q (hZ.isInitial.to Y) :=
  pullback.map p (hZ.isInitial.to Y) q (hZ.isInitial.to Y)
    f (𝟙 Z) (𝟙 Y) (by simpa using hf.symm) (by simp)

/-- The original first fibre projection retains the supplied whole source map. -/
@[reassoc (attr := simp)]
theorem fiberMap_fst {A B Y : C} (p : A ⟶ Y) (q : B ⟶ Y) (f : A ⟶ B) (hf : f ≫ q = p) :
    fiberMap Z hZ p q f hf ≫ pullback.fst q (hZ.isInitial.to Y) =
      pullback.fst p (hZ.isInitial.to Y) ≫ f :=
  pullback.lift_fst _ _ _

/-- The original second fibre projection retains the same original zero map. -/
@[reassoc (attr := simp)]
theorem fiberMap_snd {A B Y : C} (p : A ⟶ Y) (q : B ⟶ Y) (f : A ⟶ B) (hf : f ≫ q = p) :
    fiberMap Z hZ p q f hf ≫ pullback.snd q (hZ.isInitial.to Y) =
      pullback.snd p (hZ.isInitial.to Y) := by
  simpa only [Category.comp_id] using
    (show fiberMap Z hZ p q f hf ≫ pullback.snd q (hZ.isInitial.to Y) =
      pullback.snd p (hZ.isInitial.to Y) ≫ 𝟙 Z from pullback.lift_snd _ _ _)

/-- The actual fibre map is weak at fibrations with the same fibrant target. -/
theorem fiberMap_weak {A B Y : C} (p : A ⟶ Y) (q : B ⟶ Y) (f : A ⟶ B) (hf : f ≫ q = p)
    [Fibration p] [Fibration q] [WeakEquivalence f] [IsFibrant Y] :
    WeakEquivalence (fiberMap Z hZ p q f hf) := by
  let : IsFibrant Z := (isFibrant_iff_of_isTerminal (𝟙 Z) hZ.isTerminal).mpr (by infer_instance)
  let : IsCofibrant (op Y) := op_isCofibrant Y
  let : IsCofibrant (op Z) := op_isCofibrant Z
  let : Cofibration p.op := (cofibration_op_iff _).mpr inferInstance
  let : Cofibration q.op := (cofibration_op_iff _).mpr inferInstance
  let : WeakEquivalence (f.op) := (weakEquivalences_op_iff _).mpr inferInstance
  let : WeakEquivalence (𝟙 (op Y)) :=
    (weakEquivalence_iff _).mpr ((weakEquivalences Cᵒᵖ).of_isIso _)
  let : WeakEquivalence (𝟙 (op Z)) :=
    (weakEquivalence_iff _).mpr ((weakEquivalences Cᵒᵖ).of_isIso _)
  have h : WeakEquivalence ((fiberMap Z hZ p q f hf).op) :=
    weakEquivalence_map_of_isPushouts_of_cofibrant
      (IsPullback.of_hasPullback q (hZ.isInitial.to Y)).op.flip
      (IsPullback.of_hasPullback p (hZ.isInitial.to Y)).op.flip
      (a := 𝟙 (op Y)) (b := f.op) (c := 𝟙 (op Z))
      (d := (fiberMap Z hZ p q f hf).op)
      (by simpa using congrArg Quiver.Hom.op hf)
      (by simp)
      (by simpa only [op_comp] using congrArg Quiver.Hom.op (fiberMap_fst Z hZ p q f hf))
      (by simpa only [op_comp, Category.id_comp] using congrArg Quiver.Hom.op (fiberMap_snd Z hZ p q f hf))
  exact (weakEquivalences_op_iff _).mp h

end FiberMaps

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z) {Y : C} (P : PathObject Y)

local notation "J" => GeneratedArrowFactorizations.fibrant g
local notation "E" => OriginalGoodPathFiberGeometry.basedPath Z hZ P
local notation "e" => OriginalGoodPathFiberGeometry.zeroInsertion Z hZ P
local notation "pE" => OriginalGoodPathFiberGeometry.projection Z hZ P
local notation "H" => toHomotopyCategory C

/-- The literal entire based good-path Arrow, before any new factorization. -/
def basedArrow : Arrow C := Arrow.mk pE

/-- The original J factory's actual middle object on the complete based projection. -/
def middle : C := (J).Z.obj (basedArrow Z hZ P)

/-- The actual original J left factor retains the entire supplied based path object. -/
def middleLeft : E ⟶ middle g Z hZ P := (J).i.app (basedArrow Z hZ P)

/-- The actual original J right factor retains the same original target. -/
def middleRight : middle g Z hZ P ⟶ Y := (J).p.app (basedArrow Z hZ P)

/-- Both original J factor arrows recover the complete based path projection. -/
theorem middle_fac : middleLeft g Z hZ P ≫ middleRight g Z hZ P = pE :=
  (J).fac_app

/-- The full natural zero-to-based-path square is the input to the same original J factory. -/
def zeroToBasedArrow : (OriginalOrdinaryJPathCone.initialArrowFunctor Z hZ).obj Y ⟶
    basedArrow Z hZ P :=
  Arrow.homMk e (𝟙 Y) (by
    change e ≫ pE = hZ.isInitial.to Y ≫ 𝟙 Y
    simp)

/-- The original J path object maps by the original J middle functor on that whole square. -/
def originalToMiddle : (OriginalOrdinaryJPathCone.pathObject g Z hZ).obj Y ⟶ middle g Z hZ P :=
  (J).Z.map (zeroToBasedArrow Z hZ P)

/-- The complete original zero insertion square is retained in the actual middle map. -/
theorem originalToMiddle_insertion :
    (OriginalOrdinaryJPathCone.insertion g Z hZ).app Y ≫ originalToMiddle g Z hZ P =
      e ≫ middleLeft g Z hZ P :=
  ((J).i.naturality (zeroToBasedArrow Z hZ P)).symm

/-- The complete original fibration projection square is retained in the actual middle map. -/
theorem originalToMiddle_projection :
    originalToMiddle g Z hZ P ≫ middleRight g Z hZ P =
      (OriginalOrdinaryJPathCone.projection g Z hZ).app Y := by
  have h := (J).p.naturality (zeroToBasedArrow Z hZ P)
  change originalToMiddle g Z hZ P ≫ middleRight g Z hZ P =
    (OriginalOrdinaryJPathCone.projection g Z hZ).app Y ≫ 𝟙 Y at h
  erw [Category.comp_id] at h
  exact h

/-- The original middle left factor lies in the actual same-model trivial-cofibration class. -/
theorem middleLeft_trivialCofibration :
    trivialCofibrations C (middleLeft g Z hZ P) := (J).hi (basedArrow Z hZ P)

/-- The original middle right factor lies in the actual same-model fibration class. -/
theorem middleRight_fibration : fibrations C (middleRight g Z hZ P) := (J).hp (basedArrow Z hZ P)

variable [IsFibrant Y] [P.IsGood]

/-- The full original-to-middle map is weak by the same original two zero insertions. -/
theorem originalToMiddle_weak : WeakEquivalence (originalToMiddle g Z hZ P) := by
  let : WeakEquivalence ((OriginalOrdinaryJPathCone.insertion g Z hZ).app Y) :=
    (weakEquivalence_iff _).mpr (OriginalOrdinaryJPathCone.insertion_weak g Z hZ Y)
  let : WeakEquivalence e := OriginalGoodPathFiberGeometry.zeroInsertion_weak Z hZ P
  let : WeakEquivalence (middleLeft g Z hZ P) :=
    (weakEquivalence_iff _).mpr (middleLeft_trivialCofibration g Z hZ P).2
  exact weakEquivalence_of_precomp_of_fac (originalToMiddle_insertion g Z hZ P)

omit [P.IsGood] in
/-- The whole same original middle object is fibrant by its actual right factor. -/
theorem middle_isFibrant : IsFibrant (middle g Z hZ P) := by
  let : Fibration (middleRight g Z hZ P) :=
    (fibration_iff _).mpr (middleRight_fibration g Z hZ P)
  exact isFibrant_of_fibration (middleRight g Z hZ P)

end HomotopicalAlgebra.OriginalOrdinaryJLoopComparison

namespace HomotopicalAlgebra.OriginalOrdinaryJLoopComparison

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ) (Z : C) (hZ : IsZero Z)

local notation "H" => toHomotopyCategory C

/-- The full original J loop carrier's path leg is the original opposite-suspension cone leg. -/
def loopPathLeg (Y : C) :
    OriginalOrdinaryCovariantPuppeConnection.loopObject g Z hZ Y ⟶
      (OriginalOrdinaryJPathCone.pathObject g Z hZ).obj Y :=
  (OrdinaryHoChosenPuppe.suspensionCone
    (OriginalOrdinaryJPathCone.oppositeCone g Z hZ)
    (OriginalOrdinaryJPathCone.oppositeInclusion g Z hZ)
    (OriginalOrdinaryJPathCone.oppositeCofiberCocone g Z hZ) (op Z) hZ.op (op Y)).inl.unop

/-- The full original J loop carrier retains the same original caller zero leg. -/
def loopZeroLeg (Y : C) :
    OriginalOrdinaryCovariantPuppeConnection.loopObject g Z hZ Y ⟶ Z :=
  (OrdinaryHoChosenPuppe.suspensionCone
    (OriginalOrdinaryJPathCone.oppositeCone g Z hZ)
    (OriginalOrdinaryJPathCone.oppositeInclusion g Z hZ)
    (OriginalOrdinaryJPathCone.oppositeCofiberCocone g Z hZ) (op Z) hZ.op (op Y)).inr.unop

/-- The actual original J loop carrier is the entire limiting fibre of its original projection. -/
theorem loop_isPullback (Y : C) :
    IsPullback (loopPathLeg g Z hZ Y) (loopZeroLeg g Z hZ Y)
      ((OriginalOrdinaryJPathCone.projection g Z hZ).app Y) (hZ.isInitial.to Y) := by
  have h : (OrdinaryHoChosenPuppe.toZero (op Z) hZ.op (op Y)).unop = hZ.isInitial.to Y :=
    hZ.isInitial.hom_ext _ _
  have hp : IsPullback (loopPathLeg g Z hZ Y) (loopZeroLeg g Z hZ Y)
      ((OriginalOrdinaryJPathCone.projection g Z hZ).app Y)
      (OrdinaryHoChosenPuppe.toZero (op Z) hZ.op (op Y)).unop := by
    simpa only [loopPathLeg, loopZeroLeg, OrdinaryHoChosenPuppe.suspensionCone,
      Quiver.Hom.op_unop] using
      (OriginalOrdinaryJPathCone.oppositeCofiber_isPullback g Z hZ
        (OrdinaryHoChosenPuppe.toZero (op Z) hZ.op (op Y)).unop).flip
  rw [h] at hp
  exact hp

/-- The full original J fibre, with the original path projection and caller zero map. -/
abbrev originalFiber (Y : C) : C :=
  pullback ((OriginalOrdinaryJPathCone.projection g Z hZ).app Y) (hZ.isInitial.to Y)

/-- The entire original J loop carrier compares to that same actual original fibre. -/
def loopIsoFiber (Y : C) :
    OriginalOrdinaryCovariantPuppeConnection.loopObject g Z hZ Y ≅ originalFiber g Z hZ Y :=
  (loop_isPullback g Z hZ Y).isoIsPullback _ _
    (IsPullback.of_hasPullback ((OriginalOrdinaryJPathCone.projection g Z hZ).app Y)
      (hZ.isInitial.to Y))

/-- The complete carrier isomorphism retains the actual original path leg. -/
@[reassoc (attr := simp)]
theorem loopIsoFiber_fst (Y : C) :
    (loopIsoFiber g Z hZ Y).hom ≫
        pullback.fst ((OriginalOrdinaryJPathCone.projection g Z hZ).app Y) (hZ.isInitial.to Y) =
      loopPathLeg g Z hZ Y :=
  (loop_isPullback g Z hZ Y).isoIsPullback_hom_fst _ _ _

/-- The complete carrier isomorphism retains the same original zero leg. -/
@[reassoc (attr := simp)]
theorem loopIsoFiber_snd (Y : C) :
    (loopIsoFiber g Z hZ Y).hom ≫
        pullback.snd ((OriginalOrdinaryJPathCone.projection g Z hZ).app Y) (hZ.isInitial.to Y) =
      loopZeroLeg g Z hZ Y :=
  (loop_isPullback g Z hZ Y).isoIsPullback_hom_snd _ _ _

variable {Y : C} (P : PathObject Y)

/-- The full original mixed J fibre retains the actual original middle right factor. -/
abbrev middleFiber : C := pullback (middleRight g Z hZ P) (hZ.isInitial.to Y)

/-- The full actual original J fibre map is induced by the original whole middle comparison. -/
def originalFiberToMiddle : originalFiber g Z hZ Y ⟶ middleFiber g Z hZ P :=
  fiberMap Z hZ ((OriginalOrdinaryJPathCone.projection g Z hZ).app Y)
    (middleRight g Z hZ P) (originalToMiddle g Z hZ P) (originalToMiddle_projection g Z hZ P)

/-- The full actual based fibre map is induced by the same original J left factor. -/
def basedFiberToMiddle : OriginalGoodPathFiberGeometry.basedFiber Z hZ P ⟶ middleFiber g Z hZ P :=
  fiberMap Z hZ (OriginalGoodPathFiberGeometry.projection Z hZ P) (middleRight g Z hZ P)
    (middleLeft g Z hZ P) (middle_fac g Z hZ P)

variable [IsFibrant Y] [P.IsGood]

/-- The actual original J fibre comparison is weak by its original fibrations and the opposite cube. -/
theorem originalFiberToMiddle_weak : WeakEquivalence (originalFiberToMiddle g Z hZ P) := by
  let : IsFibrant ((𝟭 C).obj Y) := inferInstanceAs (IsFibrant Y)
  let : Fibration ((OriginalOrdinaryJPathCone.projection g Z hZ).app Y) :=
    (fibration_iff _).mpr (OriginalOrdinaryJPathCone.projection_fibration g Z hZ Y)
  let : Fibration (middleRight g Z hZ P) :=
    (fibration_iff _).mpr (middleRight_fibration g Z hZ P)
  let : WeakEquivalence (originalToMiddle g Z hZ P) := originalToMiddle_weak g Z hZ P
  exact fiberMap_weak Z hZ _ _ _ _

/-- The actual based fibre comparison is weak by its earned based fibration and original J factor. -/
theorem basedFiberToMiddle_weak : WeakEquivalence (basedFiberToMiddle g Z hZ P) := by
  let : Fibration (OriginalGoodPathFiberGeometry.projection Z hZ P) :=
    OriginalGoodPathFiberGeometry.projection_fibration Z hZ P
  let : Fibration (middleRight g Z hZ P) :=
    (fibration_iff _).mpr (middleRight_fibration g Z hZ P)
  let : WeakEquivalence (middleLeft g Z hZ P) :=
    (weakEquivalence_iff _).mpr (middleLeft_trivialCofibration g Z hZ P).2
  exact fiberMap_weak Z hZ _ _ _ _

private def weakImageIso {A B : C} (f : A ⟶ B) [WeakEquivalence f] :
    (H).obj A ≅ (H).obj B := by
  let : IsIso ((H).map f) := (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp
    ((weakEquivalence_iff _).mp inferInstance)
  exact asIso ((H).map f)

/-- The full original fibre comparison has an earned original-Ho isomorphism. -/
def originalFiberIsoMiddle : (H).obj (originalFiber g Z hZ Y) ≅ (H).obj (middleFiber g Z hZ P) := by
  let : WeakEquivalence (originalFiberToMiddle g Z hZ P) := originalFiberToMiddle_weak g Z hZ P
  exact weakImageIso (originalFiberToMiddle g Z hZ P)

/-- The full original based fibre comparison has an earned original-Ho isomorphism. -/
def basedFiberIsoMiddle :
    (H).obj (OriginalGoodPathFiberGeometry.basedFiber Z hZ P) ≅ (H).obj (middleFiber g Z hZ P) := by
  let : WeakEquivalence (basedFiberToMiddle g Z hZ P) := basedFiberToMiddle_weak g Z hZ P
  exact weakImageIso (basedFiberToMiddle g Z hZ P)

/-- Every map in the full comparison is an actual original limiting map or earned weak comparison. -/
def loopHoIsoPathFiber :
    (H).obj (OriginalOrdinaryCovariantPuppeConnection.loopObject g Z hZ Y) ≅
      (H).obj (OriginalGoodPathFiberGeometry.pathFiber Z hZ P) :=
  (H).mapIso (loopIsoFiber g Z hZ Y) ≪≫ originalFiberIsoMiddle g Z hZ P ≪≫
    (basedFiberIsoMiddle g Z hZ P).symm ≪≫
    (H).mapIso (OriginalGoodPathFiberGeometry.basedFiberIsoPathFiber Z hZ P)

end HomotopicalAlgebra.OriginalOrdinaryJLoopComparison

namespace HomotopicalAlgebra.OriginalOrdinaryJLoopComparison

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasZeroObject C]
  (Z : C) (hZ : IsZero Z)

/-- The zero morphisms of the original source category. -/
local instance sourceZeroMorphisms : HasZeroMorphisms C := HasZeroObject.zeroMorphismsOfZeroObject
local notation "H" => toHomotopyCategory C

/-- The complete caller-zero fibre compares to the original frame fibre by the actual zero-object isomorphism. -/
def framePathFiberIsoOriginal (D : GeneratedFunctorialReplacements.Data (C := C)) (Y : C) :
    OriginalGoodPathFiberGeometry.pathFiber Z hZ (PointedFramingAction.rightPath D Y) ≅
      DerivedSuspensionLoopAdjunction.originalPathFiber D Y := by
  let m := pullback.map (PointedFramingAction.rightPath D Y).p
    (OriginalGoodPathFiberGeometry.zeroPair Z hZ (D.R.obj Y))
    (DerivedSuspensionLoopAdjunction.originalPathBoundary D Y)
    (0 : (0 : C) ⟶ D.R.obj Y ⨯ D.R.obj Y)
    (𝟙 (PointedFramingAction.rightPath D Y).P) hZ.isoZero.hom (𝟙 (D.R.obj Y ⨯ D.R.obj Y))
    (by simp only [Category.id_comp, Category.comp_id]; rfl) (hZ.isInitial.hom_ext _ _)
  let : IsIso m := by
    dsimp only [m]
    exact pullback.map_isIso _ _ _ _ _ _ _ _ _
  exact asIso m

/-- The whole original path projection is retained in the caller-zero comparison. -/
@[reassoc (attr := simp)]
theorem framePathFiberIsoOriginal_fst (D : GeneratedFunctorialReplacements.Data (C := C)) (Y : C) :
    (framePathFiberIsoOriginal Z hZ D Y).hom ≫
        DerivedSuspensionLoopAdjunction.originalPathProjection D Y =
      pullback.fst (PointedFramingAction.rightPath D Y).p
        (OriginalGoodPathFiberGeometry.zeroPair Z hZ (D.R.obj Y)) := by
  simpa only [Category.comp_id] using
    (show (framePathFiberIsoOriginal Z hZ D Y).hom ≫
      DerivedSuspensionLoopAdjunction.originalPathProjection D Y =
        pullback.fst (PointedFramingAction.rightPath D Y).p
          (OriginalGoodPathFiberGeometry.zeroPair Z hZ (D.R.obj Y)) ≫
            𝟙 (PointedFramingAction.rightPath D Y).P from pullback.lift_fst _ _ _)

/-- The whole same caller zero projection retains its actual chosen-zero isomorphism. -/
@[reassoc (attr := simp)]
theorem framePathFiberIsoOriginal_snd (D : GeneratedFunctorialReplacements.Data (C := C)) (Y : C) :
    (framePathFiberIsoOriginal Z hZ D Y).hom ≫
        pullback.snd (DerivedSuspensionLoopAdjunction.originalPathBoundary D Y)
          (0 : (0 : C) ⟶ D.R.obj Y ⨯ D.R.obj Y) =
      pullback.snd (PointedFramingAction.rightPath D Y).p
        (OriginalGoodPathFiberGeometry.zeroPair Z hZ (D.R.obj Y)) ≫ hZ.isoZero.hom :=
  pullback.lift_snd _ _ _

variable [HasLimitsOfSize.{0, v} C] [HasColimitsOfSize.{0, v} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (g : CofibrantGenerationData C κ)

/-- The actual original derived ordinary loops compare to the original J carrier at the same original R object. -/
def loopsIsoJ (Y : C) :
    (DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)).obj
        ((H).obj Y) ≅
      (H).obj (OriginalOrdinaryCovariantPuppeConnection.loopObject g Z hZ
        ((GeneratedFunctorialReplacements.fromGeneration g).R.obj Y)) := by
  let D := GeneratedFunctorialReplacements.fromGeneration g
  let : IsFibrant (D.R.obj Y) := D.r_fibrant Y
  exact DerivedSuspensionLoopAdjunction.loopsPathIso D Y ≪≫
    ((H).mapIso (framePathFiberIsoOriginal Z hZ D Y)).symm ≪≫
      (loopHoIsoPathFiber g Z hZ (PointedFramingAction.rightPath D Y)).symm

variable (Y : C) {X : C}
  (p : X ⟶ (GeneratedFunctorialReplacements.fromGeneration g).R.obj Y) [Fibration p]
  (s : PullbackCone p (hZ.isInitial.to ((GeneratedFunctorialReplacements.fromGeneration g).R.obj Y)))
  (hs : IsLimit s)

/-- The original covariant Puppe boundary becomes a map from the actual derived ordinary loops into the same fibre. -/
def derivedConnectingToFiber :
    (DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)).obj
        ((H).obj Y) ⟶ (H).obj s.pt := by
  let : IsFibrant ((GeneratedFunctorialReplacements.fromGeneration g).R.obj Y) :=
    (GeneratedFunctorialReplacements.fromGeneration g).r_fibrant Y
  exact (loopsIsoJ Z hZ g Y).hom ≫
    OriginalOrdinaryCovariantPuppeConnection.connectingToFiber g Z hZ p s hs

/-- The complete derived ordinary connecting image is the null kernel of the original caller fibre projection. -/
theorem exact_at_fiber_from_loops (K : C) [IsCofibrant K] (f : (H).obj K ⟶ (H).obj s.pt) :
    (∃ l : (H).obj K ⟶
      (DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)).obj
        ((H).obj Y), l ≫ derivedConnectingToFiber Z hZ g Y p s hs = f) ↔
      f ≫ (H).map s.fst = OriginalOrdinaryCovariantPuppeConnection.null Z hZ K X := by
  let : IsFibrant ((GeneratedFunctorialReplacements.fromGeneration g).R.obj Y) :=
    (GeneratedFunctorialReplacements.fromGeneration g).r_fibrant Y
  let e := loopsIsoJ Z hZ g Y
  have hImage :
      (∃ l : (H).obj K ⟶
        (DerivedSuspensionLoopAdjunction.loops (GeneratedFunctorialReplacements.fromGeneration g)).obj
          ((H).obj Y), l ≫ derivedConnectingToFiber Z hZ g Y p s hs = f) ↔
      (∃ l : (H).obj K ⟶ (H).obj
        (OriginalOrdinaryCovariantPuppeConnection.loopObject g Z hZ
          ((GeneratedFunctorialReplacements.fromGeneration g).R.obj Y)),
        l ≫ OriginalOrdinaryCovariantPuppeConnection.connectingToFiber g Z hZ p s hs = f) := by
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨l ≫ e.hom, ?_⟩
      simpa only [derivedConnectingToFiber, e, Category.assoc] using hl
    · rintro ⟨l, hl⟩
      refine ⟨l ≫ e.inv, ?_⟩
      simpa only [derivedConnectingToFiber, e, Category.assoc, Iso.inv_hom_id_assoc] using hl
  exact hImage.trans (OriginalOrdinaryCovariantPuppeConnection.exact_at_fiber g Z hZ p s hs K f)

end HomotopicalAlgebra.OriginalOrdinaryJLoopComparison
