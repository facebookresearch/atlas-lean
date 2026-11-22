/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeStableCofiberIntegerExactness
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeStableCofiberIntegerMaps
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.OriginalBasedPathCoefficientGeometry
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeKan
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ChosenFiberIntegerNaturality
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableHomotopy.ISuspensionIntegerPi
import Mathlib.Algebra.FiveLemma

/-!
# The original native fiber/cofiber integer comparison

The original level-fibration fiber is restricted through the actual
sequential enriched index map, retaining its chosen point and both
projections. Its original integer connecting maps use those same
restricted cones. The full comparison uses the original I-Q suspension
unit and the actual suspended-fiber map.
-/

set_option autoImplicit false
noncomputable section
universe u v w z
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.NativeFiberCofiberIntegerComparison

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OriginalFiberCofiberGeometry
open PointedCGWH.SequentialSpectrum.StableHomotopy
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  (j : EnrichedFunctor PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v} I)

attribute [local instance] Native.modelCategory Native.allObjectsFibrant

private abbrev C := EnrichedFunctorCat PointedCGWH.{u, v} I
private abbrev underlyingSequential
    (k : EnrichedFunctor PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v} I) :=
  EnrichedFunctorCat.restriction k
private abbrev integerPiFunctor
    (k : EnrichedFunctor PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v} I)
    (q : ℤ) := NativeStableCofiberIntegerMaps.integerPiFunctor k q
private abbrev U := underlyingSequential j
private abbrev H := toHomotopyCategory (C (I := I))
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := I)
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := I)
private abbrev S := OriginalISuspension.suspension (B := B) (I := I)
private abbrev P := OrdinaryHoChosenFiberMaps.fibrantFibrationProperty (C := (C (I := I)))

/-- Every original level fibration, with the native fibrant-target proof. -/
abbrev Fibrations := (P (I := I)).FullSubcategory

omit B in
private theorem underlyingZero_isZero :
    IsZero ((U j).obj (Diagrams.zeroDiagram (A := I))) :=
  CategoryTheory.EnrichedZeroCompletion.diagram_isZero_of_obj_isZero _
    (fun n => Diagrams.initialDiagram_component_isZero (j.obj n))

omit B in
/-- The zero comparison is constructed from the literal restricted native zero. -/
def underlyingZeroIso :
    (U j).obj (Diagrams.zeroDiagram (A := I)) ≅ Diagrams.zeroDiagram
      (A := PointedCGWH.Spectra.Sequential.Index.{u, v}) :=
  (underlyingZero_isZero j).iso Diagrams.zeroDiagram_isZero

omit B in
private theorem underlying_zeroTo (Y : (C (I := I))) :
    (underlyingZeroIso j).hom ≫ Diagrams.zeroTo ((U j).obj Y) =
      (U j).map (Diagrams.zeroTo Y) :=
  (underlyingZero_isZero j).eq_of_src _ _

omit B in
/-- Restriction keeps the caller's full fiber point and both original projection maps. -/
abbrev underlyingFiberCone {X Y : (C (I := I))} (p : X ⟶ Y)
    (c : PullbackCone p (Diagrams.zeroTo Y)) :
    PullbackCone ((U j).map p) (Diagrams.zeroTo ((U j).obj Y)) :=
  PullbackCone.mk ((U j).map c.fst)
    ((U j).map c.snd ≫ (underlyingZeroIso j).hom)
    (by
      rw [← (U j).map_comp, c.condition, (U j).map_comp,
        ← underlying_zeroTo j Y, Category.assoc])

omit B in
private theorem underlying_preservesLimits : PreservesLimits (U j) :=
  (EnrichedFunctorCat.leftKanRestrictionAdjunction j).rightAdjoint_preservesLimits

attribute [local instance] underlying_preservesLimits

omit B in
private def originalZeroCone {X Y : (C (I := I))} (p : X ⟶ Y)
    (t : PullbackCone ((U j).map p) (Diagrams.zeroTo ((U j).obj Y))) :
    PullbackCone ((U j).map p) ((U j).map (Diagrams.zeroTo Y)) :=
  PullbackCone.mk t.fst (t.snd ≫ (underlyingZeroIso j).inv)
    (by
      rw [Category.assoc, ← underlying_zeroTo j Y,
        Iso.inv_hom_id_assoc]
      exact t.condition)

/-- The same restricted original cone has its transported full universal property. -/
def underlyingFiberConeIsLimit {X Y : (C (I := I))} (p : X ⟶ Y)
    (c : PullbackCone p (Diagrams.zeroTo Y)) (hc : IsLimit c) :
    IsLimit (underlyingFiberCone j p c) := by
  let h : IsLimit (c.map (U j)) :=
    (c.isLimitMapConeEquiv (U j)) (isLimitOfPreserves (U j) hc)
  let lift : ∀ t : PullbackCone ((U j).map p) (Diagrams.zeroTo ((U j).obj Y)),
      t.pt ⟶ (U j).obj c.pt :=
    fun t => h.lift (originalZeroCone j p t)
  refine PullbackCone.IsLimit.mk _ lift ?_ ?_ ?_
  · intro t
    exact h.fac (originalZeroCone j p t) WalkingCospan.left
  · intro t
    have hs : lift t ≫ (U j).map c.snd = t.snd ≫ (underlyingZeroIso j).inv :=
      h.fac (originalZeroCone j p t) WalkingCospan.right
    change lift t ≫ ((U j).map c.snd ≫ (underlyingZeroIso j).hom) = t.snd
    rw [← Category.assoc, hs, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro t m hmFirst hmZero
    apply PullbackCone.IsLimit.hom_ext h
    · exact hmFirst.trans (h.fac (originalZeroCone j p t) WalkingCospan.left).symm
    · have hm : m ≫ (U j).map c.snd = t.snd ≫ (underlyingZeroIso j).inv :=
        (Iso.eq_comp_inv (underlyingZeroIso j)).mpr
          (by simpa only [Category.assoc] using hmZero)
      exact hm.trans (h.fac (originalZeroCone j p t) WalkingCospan.right).symm

/-- Original native right-class membership supplies every original underlying level fibration. -/
theorem underlying_levelFibrations (F : (Fibrations (I := I))) (n : ℕ) :
    fibrations PointedCGWH.{u, v} (PointedCGWH.SequentialSpectrum.levelMap
      ((U j).map F.obj.hom) n) := by
  have h : fibrations (C (I := I)) F.obj.hom :=
    (HomotopicalAlgebra.fibration_iff _).mp F.property.1
  rw [Native.fibrations_eq, EvaluationTransfer.evaluationProperty_iff] at h
  change fibrations PointedCGWH.{u, v} (component (restrictionMap j F.obj.hom)
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n))
  rw [restrictionMap_component]
  exact h (j.obj (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n))

variable (a : ∀ F : Arrow (C (I := I)), PullbackCone F.hom (Diagrams.zeroTo F.right))
  (ha : ∀ F, IsLimit (a F))

/-- Every integer connecting map is the actual connecting map on the same restricted caller cone. -/
def fiberConnectingPlusOne (q : ℤ) (F : (Fibrations (I := I))) :
    (integerPiFunctor j (q + 1)).obj F.obj.right ⟶
      (integerPiFunctor j q).obj (a F.obj).pt :=
  PointedCGWH.SequentialSpectrum.StableHomotopy.ChosenFiberIntegerSequence.connectingPlusOne
    ((U j).map F.obj.hom) (underlyingFiberCone j F.obj.hom (a F.obj))
    (underlyingFiberConeIsLimit j F.obj.hom (a F.obj) (ha F.obj))
    (underlying_levelFibrations j F) q

omit B in
private theorem underlyingFiberMap_eq {F G : Arrow (C (I := I))} (m : F ⟶ G) :
    (U j).map (Diagrams.FiberGeometry.chosenFiberMap m (a F) (a G) (ha G)) =
      Diagrams.FiberGeometry.chosenFiberMap ((U j).mapArrow.map m)
        (underlyingFiberCone j F.hom (a F)) (underlyingFiberCone j G.hom (a G))
        (underlyingFiberConeIsLimit j G.hom (a G) (ha G)) := by
  apply PullbackCone.IsLimit.hom_ext (underlyingFiberConeIsLimit j G.hom (a G) (ha G))
  · rw [Diagrams.FiberGeometry.chosenFiberMap_fst]
    change (U j).map (Diagrams.FiberGeometry.chosenFiberMap m (a F) (a G) (ha G)) ≫
        (U j).map (a G).fst = (U j).map (a F).fst ≫ (U j).map m.left
    rw [← (U j).map_comp, Diagrams.FiberGeometry.chosenFiberMap_fst, (U j).map_comp]
  · rw [Diagrams.FiberGeometry.chosenFiberMap_snd]
    change (U j).map (Diagrams.FiberGeometry.chosenFiberMap m (a F) (a G) (ha G)) ≫
        ((U j).map (a G).snd ≫ (underlyingZeroIso j).hom) =
      (U j).map (a F).snd ≫ (underlyingZeroIso j).hom
    rw [← Category.assoc, ← (U j).map_comp, Diagrams.FiberGeometry.chosenFiberMap_snd]

/-- Every original source and target Arrow component preserves the canonical fiber connection. -/
theorem fiberConnectingPlusOne_naturality (q : ℤ) {F G : (Fibrations (I := I))} (m : F ⟶ G) :
    (integerPiFunctor j (q + 1)).map m.hom.right ≫ fiberConnectingPlusOne j a ha q G =
      fiberConnectingPlusOne j a ha q F ≫
        (integerPiFunctor j q).map (Diagrams.FiberGeometry.chosenFiberMap m.hom
          (a F.obj) (a G.obj) (ha G.obj)) := by
  have h := ChosenFiberIntegerNaturality.connectingPlusOne_naturality
      ((U j).map F.obj.hom) ((U j).map G.obj.hom)
      (underlying_levelFibrations j F) (underlying_levelFibrations j G)
      ((U j).mapArrow.map m.hom)
      (underlyingFiberCone j F.obj.hom (a F.obj))
      (underlyingFiberConeIsLimit j F.obj.hom (a F.obj) (ha F.obj))
      (underlyingFiberCone j G.obj.hom (a G.obj))
      (underlyingFiberConeIsLimit j G.obj.hom (a G.obj) (ha G.obj)) q
  rw [← underlyingFiberMap_eq j a ha m.hom] at h
  exact h

/-- Exactness at the original fiber keeps that same connecting map and first projection. -/
theorem fiber_exact_at_fiber (q : ℤ) (F : (Fibrations (I := I))) :
    Function.MulExact (fiberConnectingPlusOne j a ha q F).hom
      ((integerPiFunctor j q).map (a F.obj).fst).hom :=
  PointedCGWH.SequentialSpectrum.StableHomotopy.ChosenFiberIntegerSequence.exact_at_fiber
    ((U j).map F.obj.hom) (underlyingFiberCone j F.obj.hom (a F.obj))
    (underlyingFiberConeIsLimit j F.obj.hom (a F.obj) (ha F.obj))
    (underlying_levelFibrations j F) q

/-- Exactness at the original base keeps the source map in the same successor integer degree. -/
theorem fiber_exact_at_base (q : ℤ) (F : (Fibrations (I := I))) :
    Function.MulExact ((integerPiFunctor j (q + 1)).map F.obj.hom).hom
      (fiberConnectingPlusOne j a ha q F).hom :=
  PointedCGWH.SequentialSpectrum.StableHomotopy.ChosenFiberIntegerSequence.exact_at_base
    ((U j).map F.obj.hom) (underlyingFiberCone j F.obj.hom (a F.obj))
    (underlyingFiberConeIsLimit j F.obj.hom (a F.obj) (ha F.obj))
    (underlying_levelFibrations j F) q

include ha in
/-- Exactness at the original total retains the actual caller fiber inclusion. -/
theorem fiber_exact_at_total (q : ℤ) (F : (Fibrations (I := I))) :
    Function.MulExact ((integerPiFunctor j q).map (a F.obj).fst).hom
      ((integerPiFunctor j q).map F.obj.hom).hom :=
  PointedCGWH.SequentialSpectrum.StableHomotopy.ChosenFiberIntegerSequence.exact_at_total
    ((U j).map F.obj.hom) (underlyingFiberCone j F.obj.hom (a F.obj))
    (underlyingFiberConeIsLimit j F.obj.hom (a F.obj) (ha F.obj))
    (underlying_levelFibrations j F) q

private theorem integerPiFunctor_invertsLevelWeak (q : ℤ) :
    (weakEquivalences (C (I := I))).IsInvertedBy (integerPiFunctor j q) :=
  NativeStableCofiberIntegerMaps.integerPiFunctor_invertsLevelWeak (j := j) q

omit B in
/-- The original integer groups of the actual restricted native zero are trivial. -/
theorem integerZero_subsingleton (q : ℤ) :
    Subsingleton ((integerPiFunctor j q).obj (Diagrams.zeroDiagram (A := I))) := by
  let e := (integerStablePiFunctor q).mapIso (underlyingZeroIso j)
  let _ : Subsingleton ((integerStablePiFunctor q).obj
      (Diagrams.zeroDiagram (A := PointedCGWH.Spectra.Sequential.Index.{u, v}))) :=
    ISuspensionIntegerPiGeometry.integerZero_subsingleton q
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso e.hom).1
    (Subsingleton.elim _ _)⟩

/-- An actually contractible native object has trivial original integer groups. -/
theorem contractibleInteger_subsingleton (q : ℤ) (X : (C (I := I)))
    (hX : weakEquivalences (C (I := I)) (Diagrams.toZero X)) :
    Subsingleton ((integerPiFunctor j q).obj X) := by
  let Pi := integerPiFunctor j q
  let _ : IsIso (Pi.map (Diagrams.toZero X)) :=
    integerPiFunctor_invertsLevelWeak j q _ hX
  let _ : Subsingleton (Pi.obj (Diagrams.zeroDiagram (A := I))) :=
    integerZero_subsingleton j q
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso (Pi.map (Diagrams.toZero X))).1
    (Subsingleton.elim _ _)⟩

/-- Original fiber exactness makes the same connecting function bijective
for a contractible total. -/
theorem contractibleFiberConnecting_bijective (q : ℤ) (F : (Fibrations (I := I)))
    (hF : weakEquivalences (C (I := I)) (Diagrams.toZero F.obj.left)) :
    Function.Bijective (fiberConnectingPlusOne j a ha q F).hom := by
  let _ : Subsingleton ((integerPiFunctor j (q + 1)).obj F.obj.left) :=
    contractibleInteger_subsingleton j (q + 1) F.obj.left hF
  let _ : Subsingleton ((integerPiFunctor j q).obj F.obj.left) :=
    contractibleInteger_subsingleton j q F.obj.left hF
  refine ⟨(injective_iff_map_eq_one (fiberConnectingPlusOne j a ha q F).hom).mpr ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx⟩ := (fiber_exact_at_base j a ha q F y).mp hy
    exact hx.symm.trans ((congrArg ((integerPiFunctor j (q + 1)).map F.obj.hom).hom
      (Subsingleton.elim x 1)).trans (map_one _))
  · intro x
    exact (fiber_exact_at_fiber j a ha q F x).mp (Subsingleton.elim _ _)

/-- The same actual native connecting map is an Iso for every contractible-total fibration. -/
theorem contractibleFiberConnecting_isIso (q : ℤ) (F : (Fibrations (I := I)))
    (hF : weakEquivalences (C (I := I)) (Diagrams.toZero F.obj.left)) :
    IsIso (fiberConnectingPlusOne j a ha q F) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (contractibleFiberConnecting_bijective j a ha q F hF)

/-- Every original source object and full Arrow source map. -/
abbrev sourceFunctor : (Fibrations (I := I)) ⥤ (C (I := I)) :=
  (P (I := I)).ι ⋙ Arrow.leftFunc

/-- Every original target object and full Arrow target map. -/
abbrev targetFunctor : (Fibrations (I := I)) ⥤ (C (I := I)) :=
  (P (I := I)).ι ⋙ Arrow.rightFunc

/-- The whole caller-selected native fiber functor keeps the point and both projections. -/
abbrev nativeFiberFunctor : (Fibrations (I := I)) ⥤ (C (I := I)) :=
  (P (I := I)).ι ⋙ Diagrams.FiberGeometry.chosenFiberFunctor a ha

private def fiberConnectingNatTrans (q : ℤ) :
    (targetFunctor (I := I)) ⋙ integerPiFunctor j (q + 1) ⟶
      nativeFiberFunctor a ha ⋙ integerPiFunctor j q where
  app F := fiberConnectingPlusOne j a ha q F
  naturality _ _ m := fiberConnectingPlusOne_naturality j a ha q m

open OriginalFiberCofiberGeometry.NativeBasedPathGeometry

/-- The full original path connecting transformation is an actual natural Iso. -/
def pathFiberConnectingNatIso (q : ℤ) :
    (basedPathFibrationFunctor (J := I)) ⋙
      ((targetFunctor (I := I)) ⋙ integerPiFunctor j (q + 1)) ≅
    (basedPathFibrationFunctor (J := I)) ⋙
      (nativeFiberFunctor a ha ⋙ integerPiFunctor j q) := by
  let δ := Functor.whiskerLeft (basedPathFibrationFunctor (J := I))
    (fiberConnectingNatTrans j a ha q)
  let _ : ∀ Y, IsIso (δ.app Y) := fun Y =>
    contractibleFiberConnecting_isIso j a ha q
      ((basedPathFibrationFunctor (J := I)).obj Y) (basedPathQCollapse_weak (J := I) Y)
  let _ : IsIso δ := NatIso.isIso_of_isIso_app δ
  exact asIso δ

/-- The forward path Iso is the original connecting map on the caller's unchanged cone. -/
theorem pathFiberConnectingNatIso_hom_app (q : ℤ) (Y : (C (I := I))) :
    (pathFiberConnectingNatIso j a ha q).hom.app Y =
      fiberConnectingPlusOne j a ha q ((basedPathFibrationFunctor (J := I)).obj Y) := rfl

private def pathTargetNatIso :
    (basedPathFibrationFunctor (J := I)) ⋙ (targetFunctor (I := I)) ≅ 𝟭 (C (I := I)) :=
  NatIso.ofComponents (fun Y => Iso.refl Y) (by
    intro X Y f
    change f ≫ 𝟙 Y = 𝟙 X ≫ f
    exact (Category.comp_id f).trans (Category.id_comp f).symm)

private def pathTargetIntegerNatIso (q : ℤ) :
    (basedPathFibrationFunctor (J := I)) ⋙
      ((targetFunctor (I := I)) ⋙ integerPiFunctor j q) ≅ integerPiFunctor j q :=
  (Functor.associator (basedPathFibrationFunctor (J := I))
    (targetFunctor (I := I)) (integerPiFunctor j q)).symm ≪≫
      Functor.isoWhiskerRight (pathTargetNatIso (I := I)) (integerPiFunctor j q) ≪≫
        Functor.leftUnitor (integerPiFunctor j q)

private theorem pathTargetIntegerNatIso_hom_app (q : ℤ) (Y : (C (I := I))) :
    (pathTargetIntegerNatIso j q).hom.app Y = 𝟙 ((integerPiFunctor j q).obj Y) := by
  simp only [pathTargetIntegerNatIso, pathTargetNatIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Category.id_comp]
  change (integerPiFunctor j q).map (𝟙 Y) ≫ 𝟙 _ = 𝟙 _
  rw [(integerPiFunctor j q).map_id Y, Category.id_comp]

private abbrev integerPiHoFunctor
    (k : EnrichedFunctor PointedCGWH.{u, v} PointedCGWH.Spectra.Sequential.Index.{u, v} I)
    (q : ℤ) := NativeStableCofiberIntegerMaps.integerPiHoFunctor k q

private theorem integerPiHoFunctor_original (q : ℤ) :
    (H (I := I)) ⋙ integerPiHoFunctor j q = integerPiFunctor j q :=
  NativeStableCofiberIntegerMaps.integerPiHoFunctor_original (j := j) q

private theorem integerPiHoFunctor_map (q : ℤ) {X Y : (C (I := I))} (f : X ⟶ Y) :
    (integerPiHoFunctor j q).map ((H (I := I)).map f) =
      (integerPiFunctor j q).map f :=
  NativeStableCofiberIntegerMaps.integerPiHoFunctor_map (j := j) q f

private abbrev qCounitHoIso (X : (C (I := I))) :=
  NativeStableCofiberIntegerMaps.qCounitHoIso X

attribute [local instance] Replacement.isCofibrant_cofibrantReplacement

/-- The fundamental lemma chooses an actual map through the original Q counit for any Ho arrow. -/
def homRepresentative {X Y : (C (I := I))}
    (ψ : (H (I := I)).obj X ⟶ (H (I := I)).obj Y) : (Q (I := I)).obj X ⟶ Y :=
  Classical.choose (map_surjective_of_isLocalization (H (I := I)) ((Q (I := I)).obj X) Y
    ((H (I := I)).map ((ε (I := I)).app X) ≫ ψ))

/-- Its full original represented map is the same Q counit followed by the given Ho arrow. -/
theorem homRepresentative_ho {X Y : (C (I := I))}
    (ψ : (H (I := I)).obj X ⟶ (H (I := I)).obj Y) :
    (H (I := I)).map (homRepresentative ψ) =
      (H (I := I)).map ((ε (I := I)).app X) ≫ ψ :=
  Classical.choose_spec (map_surjective_of_isLocalization (H (I := I))
    ((Q (I := I)).obj X) Y ((H (I := I)).map ((ε (I := I)).app X) ≫ ψ))

/-- The actual original integer functor transports a Ho isomorphism test to its representative. -/
theorem homRepresentative_integer_isIso (q : ℤ) {X Y : (C (I := I))}
    (ψ : (H (I := I)).obj X ⟶ (H (I := I)).obj Y)
    [hψ : IsIso ((integerPiHoFunctor j q).map ψ)] :
    IsIso ((integerPiFunctor j q).map (homRepresentative ψ)) := by
  rw [← integerPiHoFunctor_map j q (homRepresentative ψ), homRepresentative_ho,
    CategoryTheory.Functor.map_comp]
  exact IsIso.comp_isIso'
    ((integerPiHoFunctor j q).mapIso (qCounitHoIso X)).isIso_hom hψ

/-- Every original integer test passes through the same original Q representative. -/
theorem homRepresentative_all_integer_isIso {X Y : (C (I := I))}
    (ψ : (H (I := I)).obj X ⟶ (H (I := I)).obj Y)
    (hψ : ∀ q : ℤ, IsIso ((integerPiHoFunctor j q).map ψ)) (q : ℤ) :
    IsIso ((integerPiFunctor j q).map (homRepresentative ψ)) := by
  let _ := hψ q
  exact homRepresentative_integer_isIso j q ψ

/-- The original Q counit conjugates the full precomposition function on any native target. -/
theorem homRepresentative_precomp_bijective_iff {X Y : (C (I := I))}
    (ψ : (H (I := I)).obj X ⟶ (H (I := I)).obj Y) (E : (C (I := I))) :
    Function.Bijective
        (fun g : (H (I := I)).obj Y ⟶ (H (I := I)).obj E => ψ ≫ g) ↔
      Function.Bijective
        (fun g : (H (I := I)).obj Y ⟶ (H (I := I)).obj E =>
          (H (I := I)).map (homRepresentative ψ) ≫ g) := by
  let εX := qCounitHoIso X
  let e : ((H (I := I)).obj X ⟶ (H (I := I)).obj E) ≃
      ((H (I := I)).obj ((Q (I := I)).obj X) ⟶ (H (I := I)).obj E) :=
    { toFun g := εX.hom ≫ g
      invFun g := εX.inv ≫ g
      left_inv g := by
        simp only [← Category.assoc, εX.inv_hom_id, Category.id_comp]
      right_inv g := by
        simp only [← Category.assoc, εX.hom_inv_id, Category.id_comp] }
  constructor
  · intro h
    have hb := e.bijective.comp h
    change Function.Bijective
      (fun g => ((H (I := I)).map ((ε (I := I)).app X)) ≫ (ψ ≫ g)) at hb
    simpa only [homRepresentative_ho, Category.assoc] using hb
  · intro h
    refine ⟨?_, ?_⟩
    · intro g k hgk
      apply h.1
      simpa only [homRepresentative_ho, Category.assoc] using
        congrArg (((H (I := I)).map ((ε (I := I)).app X)) ≫ ·) hgk
    · intro k
      obtain ⟨g, hg⟩ := h.2 (e k)
      refine ⟨g, e.injective ?_⟩
      change (H (I := I)).map ((ε (I := I)).app X) ≫ (ψ ≫ g) = _
      simpa only [homRepresentative_ho, Category.assoc] using hg

/-- Every original Omega-target test is preserved by the actual original Ho representative. -/
theorem homRepresentative_omegaTests_iff {L : Type}
    (s : NativeStabilizationFamily.{u, v} I L) {X Y : (C (I := I))}
    (ψ : (H (I := I)).obj X ⟶ (H (I := I)).obj Y) :
    NativeK.omegaTests s (homRepresentative ψ) ↔
      ∀ E : (C (I := I)), NativeK.IsOmega s E → Function.Bijective
        (fun g : (H (I := I)).obj Y ⟶ (H (I := I)).obj E => ψ ≫ g) := by
  constructor
  · intro h E hE
    exact (homRepresentative_precomp_bijective_iff ψ E).mpr (h E hE)
  · intro h E hE
    exact (homRepresentative_precomp_bijective_iff ψ E).mp (h E hE)

private abbrev cofiber := NativeK.CofiberNullity.cofiberQ (B := B) (I := I)

private def qCofiberInclusion (F : Arrow (C (I := I))) :
    (Q (I := I)).obj F.right ⟶ (cofiber (I := I)).obj F :=
  (OriginalISuspension.cocone (B := B) ((Q (I := I)).mapArrow.obj F)).inr

/-- The original Q counit inverse precedes the same original chosen cofiber inclusion. -/
abbrev originalQCofiberInclusionHo (F : Arrow (C (I := I))) :
    (H (I := I)).obj F.right ⟶ (H (I := I)).obj ((cofiber (I := I)).obj F) :=
  (qCounitHoIso F.right).inv ≫
    (H (I := I)).map (qCofiberInclusion F)

/-- Contractibility proves an actual level-Ho Iso on the same original Q cofiber inclusion. -/
theorem originalQCofiberInclusionHo_isIso (F : Arrow (C (I := I)))
    (hF : weakEquivalences (C (I := I)) (Diagrams.toZero F.left)) :
    IsIso (originalQCofiberInclusionHo F) := by
  have hi : IsIso ((H (I := I)).map (qCofiberInclusion F)) :=
    Localization.inverts (H (I := I)) (weakEquivalences (C (I := I))) _
      (PathCoefficientGeometry.originalPlainCofiberInclusion_weak (J := I)
        ((Q (I := I)).mapArrow.obj F)
        (PathCoefficientGeometry.qSourceCollapse_weak (J := I) F.left hF))
  change IsIso ((qCounitHoIso F.right).inv ≫ _)
  exact IsIso.comp_isIso' (qCounitHoIso F.right).isIso_inv hi

private theorem qCounitHoIso_inverse_naturality {X Y : (C (I := I))} (f : X ⟶ Y) :
    (H (I := I)).map f ≫ (qCounitHoIso Y).inv =
      (qCounitHoIso X).inv ≫ (H (I := I)).map ((Q (I := I)).map f) := by
  let eX := qCounitHoIso X
  let eY := qCounitHoIso Y
  have hε := (H (I := I)).congr_map ((ε (I := I)).naturality f)
  simp only [CategoryTheory.Functor.map_comp] at hε
  change (H (I := I)).map ((Q (I := I)).map f) ≫ eY.hom =
    eX.hom ≫ (H (I := I)).map f at hε
  calc
    (H (I := I)).map f ≫ eY.inv =
        (eX.inv ≫ eX.hom) ≫ ((H (I := I)).map f ≫ eY.inv) := by
      rw [eX.inv_hom_id, Category.id_comp]
    _ = eX.inv ≫ ((eX.hom ≫ (H (I := I)).map f) ≫ eY.inv) := by
      simp only [Category.assoc]
    _ = eX.inv ≫ (((H (I := I)).map ((Q (I := I)).map f) ≫ eY.hom) ≫ eY.inv) := by
      rw [← hε]
    _ = eX.inv ≫ (H (I := I)).map ((Q (I := I)).map f) := by
      simp only [Category.assoc, eY.hom_inv_id, Category.comp_id]

/-- Both full Arrow components preserve the original Q-counit inverse and cofiber inclusion. -/
theorem originalQCofiberInclusionHo_naturality {F G : Arrow (C (I := I))} (m : F ⟶ G) :
    (H (I := I)).map m.right ≫ originalQCofiberInclusionHo G =
      originalQCofiberInclusionHo F ≫ (H (I := I)).map ((cofiber (I := I)).map m) := by
  have hi := (OrdinaryHoChosenPuppe.cofiberMap_target
    (OriginalICone.cone (B := B) (I := I))
    (OriginalICone.inclusion (B := B) (I := I))
    (OriginalISuspension.cocone (B := B) (I := I))
    (OriginalISuspension.coconeIsColimit (B := B) (I := I))
    ((Q (I := I)).mapArrow.map m)).symm
  change (Q (I := I)).map m.right ≫ qCofiberInclusion G =
    qCofiberInclusion F ≫ (cofiber (I := I)).map m at hi
  dsimp only [originalQCofiberInclusionHo]
  rw [← Category.assoc, qCounitHoIso_inverse_naturality, Category.assoc,
    ← (H (I := I)).map_comp, hi, (H (I := I)).map_comp, ← Category.assoc]

/-- The full original Q cofiber functor is restricted to the genuine level fibrations. -/
abbrev nativeCofiberFunctor : (Fibrations (I := I)) ⥤ (C (I := I)) :=
  (P (I := I)).ι ⋙ (cofiber (I := I))

private def projectedIntegerNatIso {A : Type w} [Category.{z} A]
    (F : A ⥤ (C (I := I))) (q : ℤ) :
    (F ⋙ (H (I := I))) ⋙ integerPiHoFunctor j q ≅ F ⋙ integerPiFunctor j q :=
  Functor.associator F (H (I := I)) (integerPiHoFunctor j q) ≪≫
    Functor.isoWhiskerLeft F (eqToIso (integerPiHoFunctor_original j q))

private theorem projectedIntegerNatIso_hom_app {A : Type w} [Category.{z} A]
    (F : A ⥤ (C (I := I))) (q : ℤ) (X : A) :
    (projectedIntegerNatIso j F q).hom.app X =
      𝟙 ((integerPiFunctor j q).obj (F.obj X)) := rfl

private theorem projectedIntegerNatIso_inv_app {A : Type w} [Category.{z} A]
    (F : A ⥤ (C (I := I))) (q : ℤ) (X : A) :
    (projectedIntegerNatIso j F q).inv.app X =
      𝟙 ((integerPiFunctor j q).obj (F.obj X)) := rfl

private def projectedHoNatTrans {A : Type w} [Category.{z} A]
    (F G : A ⥤ (C (I := I))) (α : F ⋙ (H (I := I)) ⟶ G ⋙ (H (I := I))) (q : ℤ) :
    F ⋙ integerPiFunctor j q ⟶ G ⋙ integerPiFunctor j q :=
  (projectedIntegerNatIso j F q).inv ≫
    Functor.whiskerRight α (integerPiHoFunctor j q) ≫ (projectedIntegerNatIso j G q).hom

private theorem projectedHoNatTrans_comp {A : Type w} [Category.{z} A]
    (F G K : A ⥤ (C (I := I)))
    (α : F ⋙ (H (I := I)) ⟶ G ⋙ (H (I := I)))
    (β : G ⋙ (H (I := I)) ⟶ K ⋙ (H (I := I))) (q : ℤ) :
    projectedHoNatTrans j F G α q ≫ projectedHoNatTrans j G K β q =
      projectedHoNatTrans j F K (α ≫ β) q := by
  apply NatTrans.ext
  funext X
  simp only [projectedHoNatTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem projectedHoNatTrans_native {A : Type w} [Category.{z} A]
    (F G : A ⥤ (C (I := I))) (α : F ⟶ G) (q : ℤ) :
    projectedHoNatTrans j F G (Functor.whiskerRight α (H (I := I))) q =
      Functor.whiskerRight α (integerPiFunctor j q) := by
  apply NatTrans.ext
  funext X
  simp only [projectedHoNatTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    projectedIntegerNatIso_inv_app, projectedIntegerNatIso_hom_app,
    integerPiHoFunctor_map j]
  exact (Category.id_comp _).trans (Category.comp_id ((integerPiFunctor j q).map (α.app X)))

private def cofiberInclusionHoNatTrans :
    (targetFunctor (I := I)) ⋙ (H (I := I)) ⟶
      (nativeCofiberFunctor (I := I)) ⋙ (H (I := I)) where
  app F := originalQCofiberInclusionHo F.obj
  naturality _ _ m := originalQCofiberInclusionHo_naturality m.hom

private def cofiberInclusionNatTrans (q : ℤ) :
    (targetFunctor (I := I)) ⋙ integerPiFunctor j q ⟶
      (nativeCofiberFunctor (I := I)) ⋙ integerPiFunctor j q :=
  (projectedIntegerNatIso j (targetFunctor (I := I)) q).inv ≫
    Functor.whiskerRight (cofiberInclusionHoNatTrans (I := I)) (integerPiHoFunctor j q) ≫
      (projectedIntegerNatIso j (nativeCofiberFunctor (I := I)) q).hom

private theorem contractibleCofiberInclusion_isIso (q : ℤ) (F : (Fibrations (I := I)))
    (hF : weakEquivalences (C (I := I)) (Diagrams.toZero F.obj.left)) :
    IsIso ((cofiberInclusionNatTrans j q).app F) := by
  let _ : IsIso (originalQCofiberInclusionHo F.obj) :=
    originalQCofiberInclusionHo_isIso F.obj hF
  change IsIso ((projectedIntegerNatIso j (targetFunctor (I := I)) q).inv.app F ≫
    (integerPiHoFunctor j q).map (originalQCofiberInclusionHo F.obj) ≫
      (projectedIntegerNatIso j (nativeCofiberFunctor (I := I)) q).hom.app F)
  exact IsIso.comp_isIso'
    ((projectedIntegerNatIso j (targetFunctor (I := I)) q).app F).isIso_inv
    (IsIso.comp_isIso'
      ((integerPiHoFunctor j q).mapIso (asIso (originalQCofiberInclusionHo F.obj))).isIso_hom
      ((projectedIntegerNatIso j (nativeCofiberFunctor (I := I)) q).app F).isIso_hom)

/-- The actual original path cofiber inclusion is a natural Iso in every original integer degree. -/
def pathCofiberInclusionNatIso (q : ℤ) :
    (basedPathFibrationFunctor (J := I)) ⋙
      ((targetFunctor (I := I)) ⋙ integerPiFunctor j q) ≅
    (basedPathFibrationFunctor (J := I)) ⋙
      ((nativeCofiberFunctor (I := I)) ⋙ integerPiFunctor j q) := by
  let ι := Functor.whiskerLeft (basedPathFibrationFunctor (J := I))
    (cofiberInclusionNatTrans j q)
  let _ : ∀ Y, IsIso (ι.app Y) := fun Y =>
    contractibleCofiberInclusion_isIso j q ((basedPathFibrationFunctor (J := I)).obj Y)
      (basedPathQCollapse_weak (J := I) Y)
  let _ : IsIso ι := NatIso.isIso_of_isIso_app ι
  exact asIso ι

/-- Its forward map keeps the same original Q inverse and full chosen cofiber inclusion. -/
theorem pathCofiberInclusionNatIso_hom_app (q : ℤ) (Y : (C (I := I))) :
    (pathCofiberInclusionNatIso j q).hom.app Y =
      (cofiberInclusionNatTrans j q).app ((basedPathFibrationFunctor (J := I)).obj Y) := rfl

/-- Both identity group comparisons retain the literal Q inverse and original cofiber map. -/
theorem pathCofiberInclusionNatIso_hom_word (q : ℤ) (Y : (C (I := I))) :
    (pathCofiberInclusionNatIso j q).hom.app Y =
      (projectedIntegerNatIso j (targetFunctor (I := I)) q).inv.app
          ((basedPathFibrationFunctor (J := I)).obj Y) ≫
        (integerPiHoFunctor j q).map (originalQCofiberInclusionHo
          ((basedPathFibrationFunctor (J := I)).obj Y).obj) ≫
        (projectedIntegerNatIso j (nativeCofiberFunctor (I := I)) q).hom.app
          ((basedPathFibrationFunctor (J := I)).obj Y) := rfl


private abbrev nativeSuspendedFiberFunctor :=
  nativeFiberFunctor a ha ⋙ ((Q (I := I)) ⋙ (S (I := I)))

private def suspendedComparisonNatTrans :
    nativeSuspendedFiberFunctor a ha ⋙ (H (I := I)) ⟶
      (nativeCofiberFunctor (I := I)) ⋙ (H (I := I)) :=
  NativeK.OriginalFiberComparison.nativeFibrationComparison (B := B) (I := I) a ha

private def fiberSuspensionIntegerNatIso (q : ℤ) :
    nativeFiberFunctor a ha ⋙ integerPiFunctor j q ≅
      nativeSuspendedFiberFunctor a ha ⋙ integerPiFunctor j (q + 1) :=
  Functor.isoWhiskerLeft (nativeFiberFunctor a ha)
      (NativeStableCofiberIntegerMaps.integerISuspensionPiNatIso (j := j) q) ≪≫
    (Functor.associator (nativeFiberFunctor a ha) ((Q (I := I)) ⋙ (S (I := I)))
      (integerPiFunctor j (q + 1))).symm

private def comparisonIntegerNatTrans (q : ℤ) :
    nativeFiberFunctor a ha ⋙ integerPiFunctor j q ⟶
      (nativeCofiberFunctor (I := I)) ⋙ integerPiFunctor j (q + 1) :=
  (fiberSuspensionIntegerNatIso j a ha q).hom ≫
    projectedHoNatTrans j (nativeSuspendedFiberFunctor a ha) (nativeCofiberFunctor (I := I))
      (suspendedComparisonNatTrans a ha) (q + 1)

/-- The full original comparison uses the same I-Q suspension and the literal native Ho arrow. -/
def comparisonIntegerMap (q : ℤ) (F : (Fibrations (I := I))) :
    (integerPiFunctor j q).obj (a F.obj).pt ⟶
      (integerPiFunctor j (q + 1)).obj ((cofiber (I := I)).obj F.obj) :=
  (comparisonIntegerNatTrans j a ha q).app F

/-- The whole original Arrow square retains both original maps of the comparison. -/
theorem comparisonIntegerMap_naturality (q : ℤ) {F G : (Fibrations (I := I))} (m : F ⟶ G) :
    (integerPiFunctor j q).map (Diagrams.FiberGeometry.chosenFiberMap m.hom
      (a F.obj) (a G.obj) (ha G.obj)) ≫ comparisonIntegerMap j a ha q G =
    comparisonIntegerMap j a ha q F ≫
      (integerPiFunctor j (q + 1)).map ((cofiber (I := I)).map m.hom) :=
  (comparisonIntegerNatTrans j a ha q).naturality m

/-- The projection comparisons are identities around the unchanged original comparison. -/
theorem comparisonIntegerMap_ho_word (q : ℤ) (F : (Fibrations (I := I))) :
    comparisonIntegerMap j a ha q F =
      (fiberSuspensionIntegerNatIso j a ha q).hom.app F ≫
        (projectedIntegerNatIso j (nativeSuspendedFiberFunctor a ha) (q + 1)).inv.app F ≫
        (integerPiHoFunctor j (q + 1)).map
          (OriginalFiberCofiberGeometry.suspendedComparison (J := I) a ha F) ≫
        (projectedIntegerNatIso j (nativeCofiberFunctor (I := I)) (q + 1)).hom.app F := rfl

private theorem fiberSuspensionIntegerNatIso_hom_app (q : ℤ) (F : (Fibrations (I := I))) :
    (fiberSuspensionIntegerNatIso j a ha q).hom.app F =
      (NativeStableCofiberIntegerMaps.integerISuspensionPiNatIso (j := j) q).hom.app
        (a F.obj).pt := by
  simp only [fiberSuspensionIntegerNatIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.associator_inv_app, Category.comp_id]
  rfl

private theorem cofiberInclusionNatTrans_app_eq_native (q : ℤ) (F : (Fibrations (I := I))) :
    (cofiberInclusionNatTrans j q).app F =
      NativeStableCofiberIntegerMaps.inclusionInteger (j := j) q F.obj := by
  simp only [cofiberInclusionNatTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    projectedIntegerNatIso_hom_app, projectedIntegerNatIso_inv_app]
  rfl

private theorem boundary_eq_original (F : Arrow (C (I := I))) :
    NativeStableCofiberIntegerMaps.boundary F =
      NativeK.OriginalFiberComparison.originalQCofiberBoundary (B := B) F := rfl

private def fiberProjectionNatTrans :
    nativeFiberFunctor a ha ⟶ sourceFunctor (I := I) where
  app F := (a F.obj).fst
  naturality F G m :=
    Diagrams.FiberGeometry.chosenFiberMap_fst m.hom (a F.obj) (a G.obj) (ha G.obj)

private abbrev nativeSuspendedSourceFunctor := (sourceFunctor (I := I)) ⋙ ((Q (I := I)) ⋙ S)

private def nativeBoundaryNatTrans :
    nativeCofiberFunctor (I := I) ⟶ nativeSuspendedSourceFunctor (I := I) where
  app F := NativeStableCofiberIntegerMaps.boundary F.obj
  naturality _ _ m := NativeStableCofiberIntegerMaps.boundary_naturality m.hom

private def sourceSuspensionIntegerNatIso (q : ℤ) :
    (sourceFunctor (I := I)) ⋙ integerPiFunctor j q ≅
      (nativeSuspendedSourceFunctor (I := I)) ⋙ integerPiFunctor j (q + 1) :=
  Functor.isoWhiskerLeft (sourceFunctor (I := I))
      (NativeStableCofiberIntegerMaps.integerISuspensionPiNatIso (j := j) q) ≪≫
    (Functor.associator (sourceFunctor (I := I)) ((Q (I := I)) ⋙ S)
      (integerPiFunctor j (q + 1))).symm

private theorem sourceSuspensionIntegerNatIso_inv_app (q : ℤ) (F : Fibrations (I := I)) :
    (sourceSuspensionIntegerNatIso j q).inv.app F =
      (NativeStableCofiberIntegerMaps.integerISuspensionPiNatIso (j := j) q).inv.app
        F.obj.left := by
  simp only [sourceSuspensionIntegerNatIso, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.associator_hom_app, Category.id_comp]
  rfl

private def nativeConnectingNatTrans (q : ℤ) :
    (nativeCofiberFunctor (I := I)) ⋙ integerPiFunctor j (q + 1) ⟶
      (sourceFunctor (I := I)) ⋙ integerPiFunctor j q :=
  Functor.whiskerRight (nativeBoundaryNatTrans (I := I)) (integerPiFunctor j (q + 1)) ≫
    (sourceSuspensionIntegerNatIso j q).inv

private def nativeOriginalConnectingNatTrans (q : ℤ) :
    (nativeCofiberFunctor (I := I)) ⋙ integerPiFunctor j (q + 1) ⟶
      (sourceFunctor (I := I)) ⋙ integerPiFunctor j q :=
  (Functor.associator (P (I := I)).ι (cofiber (I := I))
    (integerPiFunctor j (q + 1))).hom ≫
      Functor.whiskerLeft (P (I := I)).ι
        (NativeStableCofiberIntegerMaps.connectingPlusOneNatTrans (j := j) q) ≫
      (Functor.associator (P (I := I)).ι Arrow.leftFunc (integerPiFunctor j q)).inv

private theorem nativeConnectingNatTrans_eq (q : ℤ) :
    @Eq ((nativeCofiberFunctor (I := I)) ⋙ integerPiFunctor j (q + 1) ⟶
      (sourceFunctor (I := I)) ⋙ integerPiFunctor j q)
      (nativeConnectingNatTrans j q) (nativeOriginalConnectingNatTrans j q) := by
  rfl

private theorem suspendedComparison_boundary_nat :
    suspendedComparisonNatTrans a ha ≫
        Functor.whiskerRight (nativeBoundaryNatTrans (I := I)) (H (I := I)) =
      Functor.whiskerRight
        (Functor.whiskerRight (fiberProjectionNatTrans a ha) ((Q (I := I)) ⋙ S))
        (H (I := I)) := by
  apply NatTrans.ext
  funext F
  change OriginalFiberCofiberGeometry.suspendedComparison (J := I) a ha F ≫
      (H (I := I)).map (NativeStableCofiberIntegerMaps.boundary F.obj) =
    (H (I := I)).map ((S (I := I)).map ((Q (I := I)).map (a F.obj).fst))
  rw [boundary_eq_original]
  exact OriginalFiberCofiberGeometry.suspendedComparison_boundary (J := I) a ha F

private theorem fiberProjection_suspension_square (q : ℤ) :
    Functor.whiskerRight (fiberProjectionNatTrans a ha) (integerPiFunctor j q) ≫
        (sourceSuspensionIntegerNatIso j q).hom =
      (fiberSuspensionIntegerNatIso j a ha q).hom ≫
        Functor.whiskerRight
          (Functor.whiskerRight (fiberProjectionNatTrans a ha) ((Q (I := I)) ⋙ S))
          (integerPiFunctor j (q + 1)) := by
  apply NatTrans.ext
  funext F
  simp only [sourceSuspensionIntegerNatIso, fiberSuspensionIntegerNatIso, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_inv_app, Category.comp_id]
  exact (NativeStableCofiberIntegerMaps.integerISuspensionPiNatIso (j := j) q).hom.naturality
    (a F.obj).fst

private theorem comparisonIntegerNatTrans_source_square (q : ℤ) :
    comparisonIntegerNatTrans j a ha q ≫ nativeConnectingNatTrans j q =
      Functor.whiskerRight (fiberProjectionNatTrans a ha) (integerPiFunctor j q) := by
  let F := nativeSuspendedFiberFunctor a ha
  let G := nativeCofiberFunctor (I := I)
  let K := nativeSuspendedSourceFunctor (I := I)
  let ψ := suspendedComparisonNatTrans a ha
  let d := nativeBoundaryNatTrans (I := I)
  let i := Functor.whiskerRight (fiberProjectionNatTrans a ha) ((Q (I := I)) ⋙ S)
  have hRaw : projectedHoNatTrans j F G ψ (q + 1) ≫
      Functor.whiskerRight d (integerPiFunctor j (q + 1)) =
    Functor.whiskerRight i (integerPiFunctor j (q + 1)) := by
    calc
      _ = projectedHoNatTrans j F G ψ (q + 1) ≫
          projectedHoNatTrans j G K (Functor.whiskerRight d (H (I := I))) (q + 1) :=
        congrArg (projectedHoNatTrans j F G ψ (q + 1) ≫ ·)
          (projectedHoNatTrans_native j G K d (q + 1)).symm
      _ = projectedHoNatTrans j F K (ψ ≫ Functor.whiskerRight d (H (I := I)))
          (q + 1) := projectedHoNatTrans_comp j F G K ψ _ (q + 1)
      _ = projectedHoNatTrans j F K (Functor.whiskerRight i (H (I := I))) (q + 1) :=
        congrArg (fun α => projectedHoNatTrans j F K α (q + 1))
          (suspendedComparison_boundary_nat a ha)
      _ = _ := projectedHoNatTrans_native j F K i (q + 1)
  calc
    _ = (fiberSuspensionIntegerNatIso j a ha q).hom ≫
        (projectedHoNatTrans j F G ψ (q + 1) ≫
          Functor.whiskerRight d (integerPiFunctor j (q + 1))) ≫
          (sourceSuspensionIntegerNatIso j q).inv := by
      simp only [comparisonIntegerNatTrans, nativeConnectingNatTrans, F, G, ψ, d,
        Category.assoc]
    _ = (fiberSuspensionIntegerNatIso j a ha q).hom ≫
        Functor.whiskerRight i (integerPiFunctor j (q + 1)) ≫
          (sourceSuspensionIntegerNatIso j q).inv := by rw [hRaw]
    _ = (Functor.whiskerRight (fiberProjectionNatTrans a ha) (integerPiFunctor j q) ≫
        (sourceSuspensionIntegerNatIso j q).hom) ≫
          (sourceSuspensionIntegerNatIso j q).inv := by
      simpa only [i, Category.assoc] using congrArg
        (· ≫ (sourceSuspensionIntegerNatIso j q).inv)
        (fiberProjection_suspension_square j a ha q).symm
    _ = _ := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The same comparison and original cofiber connection recover the caller's first projection. -/
theorem comparisonIntegerMap_source_square (q : ℤ) (F : (Fibrations (I := I))) :
    comparisonIntegerMap j a ha q F ≫
      NativeStableCofiberIntegerMaps.connectingPlusOne (j := j) q F.obj =
        (integerPiFunctor j q).map (a F.obj).fst := by
  change (comparisonIntegerNatTrans j a ha q).app F ≫
      (nativeOriginalConnectingNatTrans j q).app F =
    (Functor.whiskerRight (fiberProjectionNatTrans a ha) (integerPiFunctor j q)).app F
  have h := NatTrans.congr_app (comparisonIntegerNatTrans_source_square j a ha q) F
  have hd := NatTrans.congr_app (nativeConnectingNatTrans_eq j q) F
  simpa only [NatTrans.comp_app, hd] using h

private abbrev T := tensorLeft (A := I) PointedCGWH.sphereOne.{u, v}
private abbrev R := cotensor (I := I) PointedCGWH.sphereOne.{u, v}
private abbrev scalarAdj := ScalarLeibniz.adjunction (A := I) PointedCGWH.sphereOne.{u, v}

omit B in
/-- The actual native scalar adjunction unit induces an Iso on each original integer group. -/
theorem scalarUnit_integer_isIso (q : ℤ) (X : (C (I := I))) :
    IsIso ((integerPiFunctor j q).map ((scalarAdj (I := I)).unit.app X)) := by
  let η := (integerPiFunctor j q).map ((scalarAdj (I := I)).unit.app X)
  let e := (NativeStableCofiberIntegerMaps.nativeScalarLoopPiNatIso (j := j) q).app
    ((T (I := I)).obj X)
  have h : (NativeStableCofiberIntegerMaps.scalarIntegerPiNatIso (j := j) q).hom.app X =
      η ≫ e.hom :=
    NativeStableCofiberIntegerMaps.scalarIntegerPiNatIso_hom_native_unit (j := j) q X
  let _ : IsIso (η ≫ e.hom) := h ▸
    ((NativeStableCofiberIntegerMaps.scalarIntegerPiNatIso (j := j) q).app X).isIso_hom
  exact IsIso.of_isIso_comp_right η e.hom

omit B in
/-- The actual triangle and signed loop naturality prove raw invertibility of the native counit. -/
theorem scalarCounit_integer_isIso (q : ℤ) (Y : (C (I := I))) :
    IsIso ((integerPiFunctor j (q + 1)).map ((scalarAdj (I := I)).counit.app Y)) := by
  let Pi := integerPiFunctor j q
  let η := Pi.map ((scalarAdj (I := I)).unit.app ((R (I := I)).obj Y))
  let εR := Pi.map ((R (I := I)).map ((scalarAdj (I := I)).counit.app Y))
  let _ : IsIso η := scalarUnit_integer_isIso j q ((R (I := I)).obj Y)
  have ht : η ≫ εR = 𝟙 (Pi.obj ((R (I := I)).obj Y)) := by
    change Pi.map ((scalarAdj (I := I)).unit.app ((R (I := I)).obj Y)) ≫
      Pi.map ((R (I := I)).map ((scalarAdj (I := I)).counit.app Y)) = _
    rw [← Pi.map_comp, (scalarAdj (I := I)).right_triangle_components]
    exact Pi.map_id ((R (I := I)).obj Y)
  let _ : IsIso (η ≫ εR) := ht.symm ▸ IsIso.id _
  have hεR : IsIso εR := IsIso.of_isIso_comp_left η εR
  let l := NativeStableCofiberIntegerMaps.nativeScalarLoopPiNatIso (j := j) q
  exact (NatIso.isIso_map_iff l ((scalarAdj (I := I)).counit.app Y)).mp hεR

omit B in
/-- The unchanged scalar suspension preserves a raw integer Iso through its actual natural unit. -/
theorem scalarSuspension_integer_isIso (q : ℤ) {X Y : (C (I := I))} (f : X ⟶ Y)
    [hf : IsIso ((integerPiFunctor j q).map f)] :
    IsIso ((integerPiFunctor j (q + 1)).map ((T (I := I)).map f)) := by
  exact (NatIso.isIso_map_iff
    (NativeStableCofiberIntegerMaps.scalarIntegerPiNatIso (j := j) q) f).mp hf

open OriginalFiberCofiberGeometry.NativeBasedPathGeometry.PathCoefficientGeometry

private theorem pathConeTarget_integer_isIso (q : ℤ) (F : (Fibrations (I := I))) :
    IsIso ((integerPiHoFunctor j (q + 1)).map
      ((H (I := I)).map (pathConeTarget (J := I) F))) := by
  let A := qLoopSource (J := I) F.obj.right
  let Pi := integerPiFunctor j (q + 1)
  let hCone : IsIso (Pi.map (ConeLiftGeometry.coneToScalarSuspension (J := I) A)) :=
    integerPiFunctor_invertsLevelWeak j (q + 1) _
      (ConeLiftGeometry.coneToScalarSuspension_weak (J := I) A)
  let _ : IsIso ((integerPiFunctor j q).map
      ((ε (I := I)).app ((R (I := I)).obj F.obj.right))) :=
    integerPiFunctor_invertsLevelWeak j q _
      (Replacement.cofibrantReplacementCounit_mem_weakEquivalences
        (B := B) (A := I) ((R (I := I)).obj F.obj.right))
  have hT : IsIso (Pi.map ((T (I := I)).map
      ((ε (I := I)).app ((R (I := I)).obj F.obj.right)))) :=
    scalarSuspension_integer_isIso j q ((ε (I := I)).app ((R (I := I)).obj F.obj.right))
  have hCounit : IsIso (Pi.map ((scalarAdj (I := I)).counit.app F.obj.right)) :=
    scalarCounit_integer_isIso j q F.obj.right
  rw [integerPiHoFunctor_map j]
  change IsIso (Pi.map (ConeLiftGeometry.coneToScalarSuspension (J := I) A ≫
    ((T (I := I)).map ((ε (I := I)).app ((R (I := I)).obj F.obj.right)) ≫
      (scalarAdj (I := I)).counit.app F.obj.right)))
  simp only [CategoryTheory.Functor.map_comp]
  exact IsIso.comp_isIso' hCone (IsIso.comp_isIso' hT hCounit)

private theorem suspendedPathQFiberMap_ho_isIso (F : (Fibrations (I := I)))
    (hF : weakEquivalences (C (I := I)) (Diagrams.toZero F.obj.left)) :
    IsIso ((H (I := I)).map ((S (I := I)).map (pathQFiberMap (J := I) a ha F))) := by
  let f := pathQFiberMap (J := I) a ha F
  let _ : WeakEquivalence f :=
    (HomotopicalAlgebra.weakEquivalence_iff _).mpr (pathQFiberMap_weak (J := I) a ha F hF)
  exact Localization.inverts (H (I := I)) (weakEquivalences (C (I := I))) _
    (NativeK.FiberHomTests.originalISuspensionMap_weak (B := B) f)

include ha in
/-- Contractibility of the total makes its literal geometric comparison a raw integer Iso. -/
theorem rawComparison_integer_isIso (q : ℤ) (F : (Fibrations (I := I)))
    (hF : weakEquivalences (C (I := I)) (Diagrams.toZero F.obj.left)) :
    IsIso ((integerPiHoFunctor j (q + 1)).map
      ((H (I := I)).map (ConeLiftGeometry.rawQFiberComparison (J := I) a F.obj))) := by
  let Pi := integerPiHoFunctor j (q + 1)
  let _ : IsIso ((H (I := I)).map ((S (I := I)).map (pathQFiberMap (J := I) a ha F))) :=
    suspendedPathQFiberMap_ho_isIso a ha F hF
  let _ : IsIso (Pi.map
      ((H (I := I)).map ((S (I := I)).map (pathQFiberMap (J := I) a ha F)))) :=
    (Pi.mapIso (asIso
      ((H (I := I)).map ((S (I := I)).map (pathQFiberMap (J := I) a ha F))))).isIso_hom
  let _ : IsIso ((H (I := I)).map (OriginalISuspension.cocone (B := B) F.obj).inr) :=
    Localization.inverts (H (I := I)) (weakEquivalences (C (I := I))) _
      (originalPlainCofiberInclusion_weak (J := I) F.obj hF)
  let _ : IsIso (Pi.map ((H (I := I)).map
      (OriginalISuspension.cocone (B := B) F.obj).inr)) :=
    (Pi.mapIso (asIso ((H (I := I)).map
      (OriginalISuspension.cocone (B := B) F.obj).inr))).isIso_hom
  let _ : IsIso (Pi.map ((H (I := I)).map (pathConeTarget (J := I) F))) :=
    pathConeTarget_integer_isIso j q F
  have h := Pi.congr_map (pathQFiberMap_comparison_ho (J := I) a ha F)
  simp only [CategoryTheory.Functor.map_comp] at h
  exact IsIso.of_isIso_fac_left h

/-- The exact original Q/corner and Q-cofiber Isos retain the same suspended comparison. -/
theorem suspendedComparison_integer_isIso (q : ℤ) (F : (Fibrations (I := I)))
    (hF : weakEquivalences (C (I := I)) (Diagrams.toZero F.obj.left)) :
    IsIso ((integerPiHoFunctor j (q + 1)).map
      (OriginalFiberCofiberGeometry.suspendedComparison (J := I) a ha F)) := by
  let Pi := integerPiHoFunctor j (q + 1)
  let β := Pi.map (OriginalFiberCofiberGeometry.suspendedComparison (J := I) a ha F)
  let eF := Pi.map
    ((NativeK.OriginalFiberComparison.originalResolvedQFiberSuspensionHoIso
      (B := B) (I := I) a ha).hom.app F)
  let eC := Pi.map
    ((NativeK.OriginalFiberComparison.QCofiberToResolutionHoIso (B := B) (I := I)).hom.app F.obj)
  have hEF : IsIso eF := (Pi.mapIso
    ((NativeK.OriginalFiberComparison.originalResolvedQFiberSuspensionHoIso
      (B := B) (I := I) a ha).app F)).isIso_hom
  have hEC : IsIso eC := (Pi.mapIso
    ((NativeK.OriginalFiberComparison.QCofiberToResolutionHoIso
      (B := B) (I := I)).app F.obj)).isIso_hom
  have hRaw : IsIso (Pi.map ((H (I := I)).map (ConeLiftGeometry.rawQFiberComparison (J := I) a
      ((NativeK.OriginalFiberComparison.resolution (B := B) (I := I)).obj F.obj)))) :=
    rawComparison_integer_isIso j a ha q ((resolvedFibrationFunctor (J := I)).obj F)
      (resolvedFibration_total_weak (J := I) F hF)
  have h := Pi.congr_map (suspendedComparison_resolution_equation (J := I) a ha F)
  simp only [CategoryTheory.Functor.map_comp] at h
  have hTail : IsIso (β ≫ eC) :=
    @IsIso.of_isIso_fac_left _ _ _ _ _ eF (β ≫ eC) _ hEF hRaw h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ β eC hEC hTail

/-- The same full projected comparison is an actual Iso for a contractible-total level fibration. -/
theorem comparisonIntegerMap_isIso_of_total_contractible (q : ℤ) (F : (Fibrations (I := I)))
    (hF : weakEquivalences (C (I := I)) (Diagrams.toZero F.obj.left)) :
    IsIso (comparisonIntegerMap j a ha q F) := by
  rw [comparisonIntegerMap_ho_word]
  exact IsIso.comp_isIso' ((fiberSuspensionIntegerNatIso j a ha q).app F).isIso_hom
    (IsIso.comp_isIso'
      ((projectedIntegerNatIso j (nativeSuspendedFiberFunctor a ha) (q + 1)).app F).isIso_inv
      (IsIso.comp_isIso' (suspendedComparison_integer_isIso j a ha q F hF)
        ((projectedIntegerNatIso j (nativeCofiberFunctor (I := I)) (q + 1)).app F).isIso_hom))

private def pathIntegerComparisonNatIso (q : ℤ) :
    (basedPathFibrationFunctor (J := I)) ⋙
      (nativeFiberFunctor a ha ⋙ integerPiFunctor j q) ≅
    (basedPathFibrationFunctor (J := I)) ⋙
      ((nativeCofiberFunctor (I := I)) ⋙ integerPiFunctor j (q + 1)) := by
  let β := Functor.whiskerLeft (basedPathFibrationFunctor (J := I))
    (comparisonIntegerNatTrans j a ha q)
  let _ : ∀ Y, IsIso (β.app Y) := fun Y =>
    comparisonIntegerMap_isIso_of_total_contractible j a ha q
      ((basedPathFibrationFunctor (J := I)).obj Y) (basedPathQCollapse_weak (J := I) Y)
  let _ : IsIso β := NatIso.isIso_of_isIso_app β
  exact asIso β

/-- The original path connecting/comparison/inclusion word is a natural target automorphism. -/
def phiNatIso (q : ℤ) : integerPiFunctor j (q + 1) ≅ integerPiFunctor j (q + 1) :=
  (pathTargetIntegerNatIso j (q + 1)).symm ≪≫ pathFiberConnectingNatIso j a ha q ≪≫
    pathIntegerComparisonNatIso j a ha q ≪≫ (pathCofiberInclusionNatIso j (q + 1)).symm ≪≫
      pathTargetIntegerNatIso j (q + 1)

private theorem phiNatIso_path_inclusion (q : ℤ) (Y : (C (I := I))) :
    (phiNatIso j a ha q).hom.app Y ≫
        (pathTargetIntegerNatIso j (q + 1)).inv.app Y ≫
        (cofiberInclusionNatTrans j (q + 1)).app ((basedPathFibrationFunctor (J := I)).obj Y) =
      (pathTargetIntegerNatIso j (q + 1)).inv.app Y ≫
        (fiberConnectingNatTrans j a ha q).app ((basedPathFibrationFunctor (J := I)).obj Y) ≫
        comparisonIntegerMap j a ha q ((basedPathFibrationFunctor (J := I)).obj Y) := by
  let E := pathTargetIntegerNatIso j (q + 1)
  let ι := pathCofiberInclusionNatIso j (q + 1)
  change (E.inv.app Y ≫ (pathFiberConnectingNatIso j a ha q).hom.app Y ≫
      (pathIntegerComparisonNatIso j a ha q).hom.app Y ≫ ι.inv.app Y ≫ E.hom.app Y) ≫
        E.inv.app Y ≫ ι.hom.app Y =
    E.inv.app Y ≫ (pathFiberConnectingNatIso j a ha q).hom.app Y ≫
      (pathIntegerComparisonNatIso j a ha q).hom.app Y
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- The actual identity-base Serre lift proves the connecting square with its constructed Phi. -/
theorem comparisonIntegerMap_left_square (q : ℤ) (F : (Fibrations (I := I))) :
    fiberConnectingPlusOne j a ha q F ≫ comparisonIntegerMap j a ha q F =
      (phiNatIso j a ha q).hom.app F.obj.right ≫
        NativeStableCofiberIntegerMaps.inclusionInteger (j := j) (q + 1) F.obj := by
  let P : Fibrations (I := I) := (basedPathFibrationFunctor (J := I)).obj F.obj.right
  let m : P ⟶ F := identityBaseSerreLiftMap (J := I) F
  let D := (targetFunctor (I := I)) ⋙ integerPiFunctor j (q + 1)
  let K := nativeFiberFunctor a ha ⋙ integerPiFunctor j q
  let Cπ := (nativeCofiberFunctor (I := I)) ⋙ integerPiFunctor j (q + 1)
  let e : D.obj P ≅ D.obj F := (pathTargetIntegerNatIso j (q + 1)).app F.obj.right
  let φ : D.obj F ⟶ D.obj F := (phiNatIso j a ha q).hom.app F.obj.right
  let dF : D.obj F ⟶ K.obj F := (fiberConnectingNatTrans j a ha q).app F
  let dP : D.obj P ⟶ K.obj P := (fiberConnectingNatTrans j a ha q).app P
  let bF : K.obj F ⟶ Cπ.obj F := (comparisonIntegerNatTrans j a ha q).app F
  let bP : K.obj P ⟶ Cπ.obj P := (comparisonIntegerNatTrans j a ha q).app P
  let iF : D.obj F ⟶ Cπ.obj F := (cofiberInclusionNatTrans j (q + 1)).app F
  let iP : D.obj P ⟶ Cπ.obj P := (cofiberInclusionNatTrans j (q + 1)).app P
  let f := K.map m
  let c := Cπ.map m
  have hRight : m.hom.right = 𝟙 F.obj.right :=
    (congrArg (fun r => r.right) (identityBaseSerreLiftMap_ι (J := I) F)).trans
      (identityBaseSerreLiftArrow_right (J := I) F)
  have ht : D.map m = e.hom :=
    ((integerPiFunctor j (q + 1)).congr_map hRight).trans
      (((integerPiFunctor j (q + 1)).map_id F.obj.right).trans
        (pathTargetIntegerNatIso_hom_app j (q + 1) F.obj.right).symm)
  have hδ : e.hom ≫ dF = dP ≫ f := by
    have h := (fiberConnectingNatTrans j a ha q).naturality m
    change D.map m ≫ dF = dP ≫ f at h
    exact (congrArg (· ≫ dF) ht).symm.trans h
  have hδ' : dF = e.inv ≫ dP ≫ f := by
    have h := congrArg (e.inv ≫ ·) hδ
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h
  have hβ : f ≫ bF = bP ≫ c := (comparisonIntegerNatTrans j a ha q).naturality m
  have hi : e.hom ≫ iF = iP ≫ c := by
    have h := (cofiberInclusionNatTrans j (q + 1)).naturality m
    change D.map m ≫ iF = iP ≫ c at h
    exact (congrArg (· ≫ iF) ht).symm.trans h
  have hi' : iF = e.inv ≫ iP ≫ c := by
    have h := congrArg (e.inv ≫ ·) hi
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h
  have hφ : φ ≫ e.inv ≫ iP = e.inv ≫ dP ≫ bP :=
    phiNatIso_path_inclusion j a ha q F.obj.right
  rw [← cofiberInclusionNatTrans_app_eq_native j (q + 1) F]
  change dF ≫ bF = φ ≫ iF
  calc
    _ = e.inv ≫ dP ≫ f ≫ bF := by rw [hδ']; simp only [Category.assoc]
    _ = e.inv ≫ dP ≫ bP ≫ c := by rw [hβ]
    _ = φ ≫ e.inv ≫ iP ≫ c := by
      simpa only [Category.assoc] using congrArg (· ≫ c) hφ.symm
    _ = _ := congrArg (φ ≫ ·) hi'.symm


/-- The actual Phi ladder makes the original projected comparison bijective in every degree. -/
theorem comparisonIntegerMap_bijective (q : ℤ) (F : (Fibrations (I := I))) :
    Function.Bijective (comparisonIntegerMap j a ha q F).hom := by
  let φX : (integerPiFunctor j (q + 1)).obj F.obj.left ⟶
      (integerPiFunctor j (q + 1)).obj F.obj.left := (phiNatIso j a ha q).hom.app F.obj.left
  let φY : (integerPiFunctor j (q + 1)).obj F.obj.right ⟶
      (integerPiFunctor j (q + 1)).obj F.obj.right := (phiNatIso j a ha q).hom.app F.obj.right
  let f := (integerPiFunctor j (q + 1)).map F.obj.hom
  let p := (integerPiFunctor j q).map F.obj.hom
  let d := fiberConnectingPlusOne j a ha q F
  let i := (integerPiFunctor j q).map (a F.obj).fst
  let c : (integerPiFunctor j (q + 1)).obj F.obj.right ⟶
      (integerPiFunctor j (q + 1)).obj ((cofiber (I := I)).obj F.obj) :=
    NativeStableCofiberIntegerMaps.inclusionInteger (j := j) (q + 1) F.obj
  let b := NativeStableCofiberIntegerMaps.connectingPlusOne (j := j) q F.obj
  let β := comparisonIntegerMap j a ha q F
  have hφ : φX ≫ f = f ≫ φY := ((phiNatIso j a ha q).hom.naturality F.obj.hom).symm
  have hc₁ : f.hom.comp φX.hom = φY.hom.comp f.hom :=
    (GrpCat.hom_comp φX f).symm.trans ((congrArg (fun m => m.hom) hφ).trans
      (GrpCat.hom_comp f φY))
  have hRow : φY ≫ c = d ≫ β :=
    (comparisonIntegerMap_left_square j a ha q F).symm
  have hc₂ : c.hom.comp φY.hom = β.hom.comp d.hom :=
    (GrpCat.hom_comp φY c).symm.trans
      ((congrArg (fun m => m.hom) hRow).trans (GrpCat.hom_comp d β))
  have hc₃ : b.hom.comp β.hom = (MonoidHom.id _).comp i.hom := by
    simpa only [GrpCat.hom_comp, MonoidHom.id_comp] using
      congrArg (fun m => m.hom) (comparisonIntegerMap_source_square j a ha q F)
  exact MonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    f.hom d.hom i.hom p.hom f.hom c.hom b.hom p.hom
    φX.hom φY.hom β.hom (MonoidHom.id _) (MonoidHom.id _)
    hc₁ hc₂ hc₃ (by simp)
    (fiber_exact_at_base j a ha q F) (fiber_exact_at_fiber j a ha q F)
    (fiber_exact_at_total j a ha q F)
    (NativeStableCofiberIntegerExactness.source_inclusion_mulExact (j := j) (q + 1) F.obj)
    (NativeStableCofiberIntegerExactness.exact_at_cofiber_plusOne (j := j) q F.obj)
    (NativeStableCofiberIntegerExactness.connectingPlusOne_source_mulExact (j := j) q F.obj)
    (ConcreteCategory.bijective_of_isIso φX).2 (ConcreteCategory.bijective_of_isIso φY)
    Function.bijective_id Function.injective_id

/-- The literal original projected comparison is an Iso on every native level fibration. -/
theorem comparisonIntegerMap_isIso (q : ℤ) (F : (Fibrations (I := I))) :
    IsIso (comparisonIntegerMap j a ha q F) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (comparisonIntegerMap_bijective j a ha q F)

/-- Every original integer functor inverts the same unchanged suspended chosen-fiber comparison. -/
theorem suspendedComparison_all_integer_isIso (q : ℤ) (F : (Fibrations (I := I))) :
    IsIso ((integerPiHoFunctor j q).map
      (OriginalFiberCofiberGeometry.suspendedComparison (J := I) a ha F)) := by
  let r := q - 1
  let ν := (fiberSuspensionIntegerNatIso j a ha r).app F
  let eS := (projectedIntegerNatIso j (nativeSuspendedFiberFunctor a ha) (r + 1)).app F
  let eC := (projectedIntegerNatIso j (nativeCofiberFunctor (I := I)) (r + 1)).app F
  let ψ := (integerPiHoFunctor j (r + 1)).map
    (OriginalFiberCofiberGeometry.suspendedComparison (J := I) a ha F)
  have hβ := comparisonIntegerMap_isIso j a ha r F
  have hword : IsIso (ν.hom ≫ eS.inv ≫ ψ ≫ eC.hom) :=
    (comparisonIntegerMap_ho_word j a ha r F) ▸ hβ
  have h₁ : IsIso (eS.inv ≫ ψ ≫ eC.hom) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ ν.hom _ ν.isIso_hom hword
  have h₂ : IsIso (ψ ≫ eC.hom) :=
    @IsIso.of_isIso_comp_left _ _ _ _ _ eS.inv _ eS.isIso_inv h₁
  have h₃ : IsIso ψ :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ ψ eC.hom eC.isIso_hom h₂
  dsimp only [ψ, r] at h₃
  have hdegree : q - 1 + 1 = q := by omega
  rw [hdegree] at h₃
  exact h₃


end HomotopicalAlgebra.EnrichedProjective.Native.NativeFiberCofiberIntegerComparison
